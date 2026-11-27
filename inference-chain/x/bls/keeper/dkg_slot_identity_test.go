package keeper

import (
	"fmt"
	"testing"

	"cosmossdk.io/math"
	bls12381 "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/require"
	blst "github.com/supranational/blst/bindings/go"

	"github.com/productscience/inference/x/bls/types"
)

// A full DKG through the message handlers at mainnet parameters (100 slots,
// degree 50): four hosts with 25 slots each, every host deals and votes, with
// real commitment proofs and real dealer validity proofs. Host 3 owns slots
// 75..99. As the owner of slot 99 it receives every dealer's share for that
// slot, so once the other parts are on chain it can deal a polynomial that
// cancels their sum there.

const (
	slotIdentityChainID  = "gonka-mainnet"
	slotIdentityTotal    = 100
	slotIdentityDegree   = 50
	slotIdentityHosts    = 4
	slotIdentityAttacker = 3
	slotIdentityTarget   = 99 // a slot of the attacker
)

type slotIdentityDKG struct {
	t            *testing.T
	k            Keeper
	ms           msgServer
	ctx          sdk.Context
	epochID      uint64
	participants []types.BLSParticipantInfo
	polys        [][]fr.Element // the polynomial each host dealt, by participant index
}

func slotIdentityParticipants(prefix string) []types.BLSParticipantInfo {
	participants := make([]types.BLSParticipantInfo, slotIdentityHosts)
	perHost := uint32(slotIdentityTotal / slotIdentityHosts)
	for i := range participants {
		participants[i] = types.BLSParticipantInfo{
			Address:            fmt.Sprintf("%shost%d", prefix, i),
			PercentageWeight:   math.LegacyNewDec(25),
			Secp256K1PublicKey: []byte(fmt.Sprintf("%spubkey%d", prefix, i)),
			SlotStartIndex:     uint32(i) * perHost,
			SlotEndIndex:       uint32(i+1)*perHost - 1,
		}
	}
	return participants
}

func newSlotIdentityDKG(t *testing.T, k Keeper, ctx sdk.Context, epochID uint64, participants []types.BLSParticipantInfo) *slotIdentityDKG {
	dealerParts := make([]*types.DealerPartStorage, len(participants))
	submissions := make([]*types.VerificationVectorSubmission, len(participants))
	for i := range participants {
		dealerParts[i] = &types.DealerPartStorage{Commitments: [][]byte{}, ParticipantShares: []*types.EncryptedSharesForParticipant{}}
		submissions[i] = &types.VerificationVectorSubmission{DealerValidity: []bool{}}
	}
	require.NoError(t, k.SetEpochBLSData(ctx, types.EpochBLSData{
		EpochId:                   epochID,
		ITotalSlots:               slotIdentityTotal,
		TSlotsDegree:              slotIdentityDegree,
		Participants:              participants,
		DkgPhase:                  types.DKGPhase_DKG_PHASE_DEALING,
		DealingPhaseDeadlineBlock: ctx.BlockHeight() + 5,
		GroupPublicKey:            []byte{},
		DealerParts:               dealerParts,
		VerificationSubmissions:   submissions,
	}))
	k.SetActiveEpochID(ctx, epochID)
	return &slotIdentityDKG{
		t: t, k: k, ms: msgServer{Keeper: k}, ctx: ctx, epochID: epochID,
		participants: participants, polys: make([][]fr.Element, len(participants)),
	}
}

func evalSlotPoly(coeffs []fr.Element, slot uint32) fr.Element {
	var x, acc fr.Element
	x.SetUint64(uint64(slot) + 1)
	for i := len(coeffs) - 1; i >= 0; i-- {
		acc.Mul(&acc, &x)
		acc.Add(&acc, &coeffs[i])
	}
	return acc
}

func randomSlotPoly(t *testing.T) []fr.Element {
	coeffs := make([]fr.Element, slotIdentityDegree+1)
	for i := range coeffs {
		_, err := coeffs[i].SetRandom()
		require.NoError(t, err)
	}
	return coeffs
}

// deal submits MsgSubmitDealerPart for host d with valid commitment proofs.
// The chain never decrypts shares, so the ciphertexts only need the right shape.
func (h *slotIdentityDKG) deal(d int, coeffs []fr.Element) error {
	addr := h.participants[d].Address
	commitments := make([][]byte, len(coeffs))
	proofs := make([]types.CommitmentKnowledgeProof, len(coeffs))
	for i := range coeffs {
		commitment, proof, err := types.BuildCommitmentKnowledgeProof(h.ctx.ChainID(), h.epochID, addr, uint32(i), &coeffs[i])
		require.NoError(h.t, err)
		commitments[i], proofs[i] = commitment, proof
	}
	shares := make([]types.EncryptedSharesForParticipant, len(h.participants))
	for j, p := range h.participants {
		ciphertexts := make([][]byte, p.SlotEndIndex-p.SlotStartIndex+1)
		for s := range ciphertexts {
			ciphertexts[s] = make([]byte, types.MinEncryptedShareCiphertextLen)
			ciphertexts[s][0], ciphertexts[s][1] = byte(d+1), byte(s)
		}
		shares[j] = types.EncryptedSharesForParticipant{EncryptedShares: ciphertexts}
	}
	_, err := h.ms.SubmitDealerPart(h.ctx, &types.MsgSubmitDealerPart{
		Creator:                        addr,
		EpochId:                        h.epochID,
		Commitments:                    commitments,
		CommitmentProofs:               proofs,
		EncryptedSharesForParticipants: shares,
	})
	if err == nil {
		h.polys[d] = coeffs
	}
	return err
}

// cancellingPoly is what the owner of `target` deals: random coefficients,
// with the constant term chosen so that its share at `target` is minus the sum
// of the shares already dealt there. It reads those shares by decrypting its
// own ciphertexts for `target`; here they come from the dealt polynomials.
func (h *slotIdentityDKG) cancellingPoly(target uint32) []fr.Element {
	var dealt fr.Element
	for _, poly := range h.polys {
		if poly != nil {
			share := evalSlotPoly(poly, target)
			dealt.Add(&dealt, &share)
		}
	}
	coeffs := randomSlotPoly(h.t)
	coeffs[0].SetZero()
	rest := evalSlotPoly(coeffs, target)
	coeffs[0].Neg(&dealt)
	coeffs[0].Sub(&coeffs[0], &rest)
	own := evalSlotPoly(coeffs, target)
	require.False(h.t, own.IsZero(), "the attacker's own share at the target slot is not zero")
	return coeffs
}

func (h *slotIdentityDKG) signSlots(messageHash []byte, slots []uint32, secret func(slot uint32) fr.Element) []byte {
	messageG1, err := h.k.hashToG1(messageHash)
	require.NoError(h.t, err)
	var sig []byte
	for _, slot := range slots {
		sig = append(sig, g1SignatureFromScalar(messageG1, secret(slot))...)
	}
	return sig
}

func (h *slotIdentityDKG) slotsOf(v int) []uint32 {
	p := h.participants[v]
	slots := make([]uint32, 0, p.SlotEndIndex-p.SlotStartIndex+1)
	for slot := p.SlotStartIndex; slot <= p.SlotEndIndex; slot++ {
		slots = append(slots, slot)
	}
	return slots
}

// vote submits an honest verification vector for host v: every dealer valid,
// with a dealer validity proof (a per-slot BLS signature under the received share) for each other dealer.
func (h *slotIdentityDKG) vote(v int) {
	validity := make([]bool, len(h.participants))
	var proofs []types.DealerValidityProof
	for d, poly := range h.polys {
		validity[d] = poly != nil
		if poly == nil || d == v {
			continue
		}
		hash := types.BuildDealerValidityProofHash(h.epochID, uint32(d))
		proofs = append(proofs, types.DealerValidityProof{
			DealerIndex:    uint32(d),
			ProofSignature: h.signSlots(hash, h.slotsOf(v), func(slot uint32) fr.Element { return evalSlotPoly(poly, slot) }),
		})
	}
	_, err := h.ms.SubmitVerificationVector(h.ctx, &types.MsgSubmitVerificationVector{
		Creator:              h.participants[v].Address,
		EpochId:              h.epochID,
		DealerValidity:       validity,
		DealerValidityProofs: proofs,
	})
	require.NoError(h.t, err)
}

func (h *slotIdentityDKG) epochData() types.EpochBLSData {
	data, err := h.k.GetEpochBLSData(h.ctx, h.epochID)
	require.NoError(h.t, err)
	return data
}

// finish runs the phase transitions at their deadlines, with every host voting in VERIFYING.
func (h *slotIdentityDKG) finish() types.EpochBLSData {
	h.ctx = h.ctx.WithBlockHeight(h.epochData().DealingPhaseDeadlineBlock)
	require.NoError(h.t, h.k.ProcessDKGPhaseTransitionForEpoch(h.ctx, h.epochID))
	require.Equal(h.t, types.DKGPhase_DKG_PHASE_VERIFYING, h.epochData().DkgPhase)

	h.ctx = h.ctx.WithBlockHeight(h.ctx.BlockHeight() + 1)
	for v := range h.participants {
		h.vote(v)
	}

	h.ctx = h.ctx.WithBlockHeight(h.epochData().VerifyingPhaseDeadlineBlock)
	require.NoError(h.t, h.k.ProcessDKGPhaseTransitionForEpoch(h.ctx, h.epochID))
	require.Equal(h.t, types.DKGPhase_DKG_PHASE_DISPUTING, h.epochData().DkgPhase)

	h.ctx = h.ctx.WithBlockHeight(h.epochData().DisputingPhaseDeadlineBlock)
	require.NoError(h.t, h.k.ProcessDKGPhaseTransitionForEpoch(h.ctx, h.epochID))
	return h.epochData()
}

func (h *slotIdentityDKG) dkgFailureReason() string {
	for _, ev := range h.ctx.EventManager().ABCIEvents() {
		msg, err := sdk.ParseTypedEvent(ev)
		if err != nil {
			continue
		}
		if failed, ok := msg.(*types.EventDKGFailed); ok && failed.EpochId == h.epochID {
			return failed.Reason
		}
	}
	return ""
}

// slotSecret is a host's secret for one slot of this epoch: the sum of the valid dealers' shares.
func (h *slotIdentityDKG) slotSecret(slot uint32) fr.Element {
	var secret fr.Element
	for _, poly := range h.polys {
		if poly != nil {
			share := evalSlotPoly(poly, slot)
			secret.Add(&secret, &share)
		}
	}
	return secret
}

// storeNextEpoch stores the next epoch with a completed DKG and a valid group key.
func (h *slotIdentityDKG) storeNextEpoch() uint64 {
	var groupSecret fr.Element
	_, err := groupSecret.SetRandom()
	require.NoError(h.t, err)
	_, _, _, g2Gen := bls12381.Generators()
	next := h.epochID + 1
	require.NoError(h.t, h.k.SetEpochBLSData(h.ctx, types.EpochBLSData{
		EpochId:                     next,
		ITotalSlots:                 slotIdentityTotal,
		TSlotsDegree:                slotIdentityDegree,
		Participants:                slotIdentityParticipants("next"),
		DkgPhase:                    types.DKGPhase_DKG_PHASE_COMPLETED,
		DisputingPhaseDeadlineBlock: h.ctx.BlockHeight(),
		GroupPublicKey:              g2BytesFromScalar(g2Gen, groupSecret),
	}))
	return next
}

// validateNext has host v of this epoch sign the next epoch's group key with its slot secrets.
func (h *slotIdentityDKG) validateNext(v int, next uint64, slots []uint32) error {
	nextData, err := h.k.GetEpochBLSData(h.ctx, next)
	require.NoError(h.t, err)
	hash, err := h.ms.computeValidationMessageHash(h.ctx, nextData.GroupPublicKey, h.epochID, next)
	require.NoError(h.t, err)
	_, err = h.ms.SubmitGroupKeyValidationSignature(h.ctx, &types.MsgSubmitGroupKeyValidationSignature{
		Creator:          h.participants[v].Address,
		NewEpochId:       next,
		SlotIndices:      slots,
		PartialSignature: h.signSlots(hash, slots, h.slotSecret),
	})
	return err
}

func requestSignature(k Keeper, ctx sdk.Context, epochID uint64, id byte) error {
	requestID := make([]byte, 32)
	requestID[31] = id
	return k.RequestThresholdSignature(ctx, types.SigningData{
		CurrentEpochId: epochID,
		ChainId:        make([]byte, 32),
		RequestId:      requestID,
		Data:           [][]byte{make([]byte, 32)},
	})
}

func setupSlotIdentityDKG(t *testing.T, epochID uint64) *slotIdentityDKG {
	k, ctx := setupTimingKeeper(t)
	ctx = ctx.WithChainID(slotIdentityChainID).WithBlockHeight(1000)
	params, err := k.GetParams(ctx)
	require.NoError(t, err)
	require.Equal(t, int64(0), params.CompletedFallbackBlocks, "mainnet runs with completed_fallback_blocks = 0")
	return newSlotIdentityDKG(t, k, ctx, epochID, slotIdentityParticipants(""))
}

func dealWithCancelledSlot(t *testing.T, h *slotIdentityDKG) {
	for d := 0; d < slotIdentityHosts; d++ {
		if d != slotIdentityAttacker {
			require.NoError(t, h.deal(d, randomSlotPoly(t)))
		}
	}
	// Accepted: the proofs are valid and the attacker's own polynomial is non-zero at every slot.
	require.NoError(t, h.deal(slotIdentityAttacker, h.cancellingPoly(slotIdentityTarget)))
}

// Control: the same DKG with an honest fourth dealer completes, and the hosts
// can validate the next epoch's group key. So the harness signs and votes correctly.
func TestDKGSlotIdentity_HonestDealersComplete(t *testing.T) {
	h := setupSlotIdentityDKG(t, 470)
	for d := 0; d < slotIdentityHosts; d++ {
		require.NoError(t, h.deal(d, randomSlotPoly(t)))
	}
	data := h.finish()
	require.Equal(t, types.DKGPhase_DKG_PHASE_COMPLETED, data.DkgPhase, h.dkgFailureReason())
	require.Len(t, data.SlotPublicKeys, slotIdentityTotal)

	next := h.storeNextEpoch()
	for v := 0; v < slotIdentityHosts-1; v++ {
		require.NoError(t, h.validateNext(v, next, h.slotsOf(v)))
	}
	nextData, err := h.k.GetEpochBLSData(h.ctx, next)
	require.NoError(t, err)
	require.Equal(t, types.DKGPhase_DKG_PHASE_SIGNED, nextData.DkgPhase)
	require.NoError(t, requestSignature(h.k, h.ctx, next, 1))
}

// A slot owner that zeroes its own slot only disables that slot: the DKG
// completes, the zeroed slot cannot sign, and the other 75 slots sign the next
// epoch's key.
func TestDKGSlotIdentity_ZeroedSlotOnlyDisablesItself(t *testing.T) {
	h := setupSlotIdentityDKG(t, 470)
	dealWithCancelledSlot(t, h)

	data := h.finish()
	require.Equal(t, types.DKGPhase_DKG_PHASE_COMPLETED, data.DkgPhase, h.dkgFailureReason())
	require.Len(t, data.SlotPublicKeys, slotIdentityTotal)
	for slot, key := range data.SlotPublicKeys {
		pk := new(blst.P2Affine).Uncompress(key)
		require.Equal(t, slot != slotIdentityTarget, pk != nil && pk.KeyValidate(), "slot %d", slot)
	}

	next := h.storeNextEpoch()
	// The zeroed slot's partial signature is rejected (its secret is zero, so the signature is the identity) ...
	require.Error(t, h.validateNext(slotIdentityAttacker, next, []uint32{slotIdentityTarget}))
	// ... and the attacker's other slots plus the honest hosts still reach t+1 = 51.
	attackerSlots := h.slotsOf(slotIdentityAttacker)
	require.NoError(t, h.validateNext(slotIdentityAttacker, next, attackerSlots[:len(attackerSlots)-1]))
	require.NoError(t, h.validateNext(0, next, h.slotsOf(0)))
	nextData, err := h.k.GetEpochBLSData(h.ctx, next)
	require.NoError(t, err)
	require.Equal(t, types.DKGPhase_DKG_PHASE_COMPLETED, nextData.DkgPhase, "49 slots are below t+1")
	require.NoError(t, h.validateNext(1, next, h.slotsOf(1)))
	nextData, err = h.k.GetEpochBLSData(h.ctx, next)
	require.NoError(t, err)
	require.Equal(t, types.DKGPhase_DKG_PHASE_SIGNED, nextData.DkgPhase)
	require.NoError(t, requestSignature(h.k, h.ctx, next, 3))
}
