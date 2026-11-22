import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
import Formalism.LocalToGlobal.KernelLattices.KerHypAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetsInOfIsTw
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwEx

open JetEx

def stepSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb (amb0 P.host) (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1) * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1))) (totDeg P k.1 k.2.1)

def allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Set ℂ :=
  ⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSet P χ k)}, stepSet P χ k

theorem finAlg_allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) : FinAlg (allSet P χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine finAlg_biUnion ?_ fun k hk => hk.2
  exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩

open Classical in

def gens (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSet P χ Ξ) then h.choose else ∅

theorem gens_algebraic (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : ∀ z ∈ gens P χ Ξ, IsAlgebraic ℚ z := by
  unfold gens
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSet_subset (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) {K : Subfield ℂ}
    (hK : ∀ z ∈ gens P χ Ξ, z ∈ K) : allSet P χ Ξ ⊆ K := by
  have h1 := finAlg_allSet P χ h
  rw [gens, dif_pos h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem jetsIn_of_isTw {B : Base} {X : PreX B.toPre} (hL : StagesInhab.HasLetters B.toPre) {I : TC B X} (h : I.Ok) (ht : I.IsTw)
    (hJ : I.J = amb0 B.host) (hK : ∀ z ∈ gens B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) :
    ColIn.JetsIn I := by
  have hall := allSet_subset B.toPre I.C.chiPsi (Set.finite_range I.xi) hK
  refine I.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_
  have hM : I.modulus a u = (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1) *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1)) := by
    have eA : (I.cst a).A = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    have eB : (I.cst a).B = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    unfold ColIn.modulus cAof cBof
    rw [eA, eB, Finset.prod_coe_sort _ qOf]
  have hS : stepSet B.toPre I.C.chiPsi (u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)) =
      jetSet I.A (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) (I.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A, hJ]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I.sel (I.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Set.mem_iUnion₂.2 ⟨(u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)),
    ⟨⟨hi, Sb_subset h a u, rowSG_subset h a⟩, ?_⟩, ?_⟩)
  · rw [hS]
    exact finAlg_step hL h a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

theorem lg_gens (K : Top.Ctx) : Top.large₂ K fun B f T => ∀ z ∈ gens B.toPre f.chiPsi (T.set f), z ∈ B.embLL.fieldRange :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => gens P f.chiPsi Ξ, by simp,
    fun P f _ _ Ξ => gens_algebraic P f.chiPsi Ξ, fun _ _ _ _ h _ _ => h.2⟩

theorem exists_quot {K : Top.Ctx} {P : Pre} (h : K.Over P) (X : PreX P) :
    ∃ X' : PreX P, X'.piG = X.piG ∧ ∀ u, P.cOf u * (X'.piT u : P.host.E) = (X'.piT P.u₀ : P.host.E) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨{ X with
    piT := K.Lv.piT
    piT_K := K.Lv.piT_K
    piT_norm := K.Lv.piT_norm
    piT_cong := fun u => Ideal.mem_span_singleton.1 (K.Lv.piT_cong u) }, rfl, fun u => ?_⟩
  exact div_mul_cancel₀ _ (K.Lv.piT_ne u)

theorem evLg_canonical : GlobalTheory.Mem.Top.EvLg fun _ B f T => (letI := B.host.cmStar; ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b → B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b) → Nonempty (PreX B.toPre) → ∀ Pv, IsSel B.fields Pv → ∃ (X : PreX B.toPre) (I : TC B X), I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ I.sel = Pv ∧ I.C = f ∧ I.S = {p | p ∈ GlobalTheory.Mem.Top.offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} ∧ Set.range I.xi = T.set f ∧ ∀ C W V S N G, Formalism.L2.Host.ValLL0 (assemble B C W V S N G) (GlobalTheory.Mem.Top.Fr.at ⟨B, C, W, V, S, N, G⟩ f) ∧ GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  refine InEx.ev_of_forall fun K => ((InEx.lg_colIn K).inter (lg_gens K)).imp fun B f T hO h hi ⟨X₀⟩ Pv hPv => ?_
  obtain ⟨X₁, hX⟩ := InEx.exists_oriented X₀ f.P
  obtain ⟨X, e, hc⟩ := exists_quot hO X₁
  have hX' : InEx.Oriented X f.P := by
    unfold InEx.Oriented at hX ⊢
    rw [e]; exact hX
  obtain ⟨I, a1, rfl, a3, a4, a5, a6, a7⟩ := h.1.1 X hX' Pv hPv (amb0 B.host) (exists_ambIn_ok B.host).choose_spec
  have hk : (canon I).Ok := canon_ok a1 fun a P hP => ((a7 a).2.2.2 P hP).ge
  exact ⟨X, canon I, hk, ⟨hi, hc⟩, canon_isTw I,
    jetsIn_of_isTw (hasLetters_of_over hO) hk (canon_isTw I) a6 (by have := h.2; rw [← a4] at this; exact this), a5, rfl, a3, a4,
    fun C W V S N G => ⟨h.1.2.1 C W V S N G, h.1.2.2⟩⟩

end GlobalTheory.Mem.Col2.TwEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Bare

open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial

def cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ H) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e.symm : MonoidAlgebra ℂ H →ₐ[ℂ] MonoidAlgebra ℂ G).comp
    (Subalgebra.center ℂ (MonoidAlgebra ℂ H)).val).codRestrict _ fun z => by
      rw [Subalgebra.mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := (MonoidAlgebra.domCongr ℂ ℂ e.symm).surjective b
      change _ * MonoidAlgebra.domCongr ℂ ℂ e.symm z = MonoidAlgebra.domCongr ℂ ℂ e.symm z * _
      rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 z.2 c]

theorem coeff_cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (g : G) :
    (cenPull e z : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g) :=
  MonoidAlgebra.coeff_domCongr (R := ℂ) e.symm (z : MonoidAlgebra ℂ H) g

theorem cenPull_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) {z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)}
    {z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)}
    (h : ∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g)) : cenPull e z = z' := by
  apply Subtype.ext
  ext g
  rw [coeff_cenPull, h]

attribute [local instance] GlobalTheory.Mem.Top.factType

set_option synthInstance.maxHeartbeats 400000 in

def reser {R : Ranks} {H : Host R} {what₂ rows' : Rows.Data R} {N : NData R H what₂} {N' : NData R H rows'} {A : NAut N} {A' : NAut N'}
    (T : NTypes A) (T' : NTypes A')
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Mt μ j)) : NTypes A :=
  { T with
    eSer := T'.eSer
    eSer_idem := T'.eSer_idem
    eSer_central := T'.eSer_central
    eSer_orth := T'.eSer_orth
    eSer_zero := T'.eSer_zero
    eSer_sum := T'.eSer_sum
    cenAmb := a
    cenMt := b }

theorem goodElement_mem_center_groupAlgebra {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : NTypes A) :
    T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  exact (TypesInhab.good_sum (I := Σ k : Fin 2, N.PlG k) (P := fun kv => Fin R.r → ZMod (H.g kv.1))
    (fun kv p => T.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => T.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) T.e0 (fun g => rfl)
    (fun _ _ => T.eSer_idem _ _) (fun _ _ => T.eSer_central _ _)
    (fun _ p q hpq => T.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))).1

theorem exists_nStage_act {B : Base} {C C₀ : Cols B} {W₀ : RowsRest B C₀} (N₀ : NStage B C₀ W₀) {f : Fr B.toPre}
    (h₀ : GrpTrue N₀ f) (W : RowsRest B C) (hsha : ShaOK B.toPre W.shaLen) (heta : ∀ j w, W.etaJ j w = 0)
    {G : Type} [Group G] (e₀ : G ≃* G0g N₀.nd)
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Mt μ j))
    (ha : ∀ z : Subalgebra.center ℂ (MonoidAlgebra ℂ G),
      (∀ g, (z : MonoidAlgebra ℂ G).coeff g = N₀.ntypes.e0.coeff (e₀ g)) → (∀ μ, W.eOp μ = a μ z) ∧ ∀ μ j, W.eMt μ j = b μ j z) :
    ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      (∀ μ z, N.ntypes.cenAmb μ z = a μ (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z)) ∧
      ∀ μ j z, N.ntypes.cenMt μ j z = b μ j (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z) := by
  obtain ⟨ldat, hsha⟩ := hsha
  let nd := trueLayer B C W f.W ldat hsha
  have hE : IsEmpty nd.Loc := ⟨fun i : Empty => i.elim⟩
  let A : NAut nd := GaloisStage.nAut nd (fun k v => above f.P (nd.g_split k) v)
    (fun k v => div_over f.P (above_div _ _ v)) (fun k => above_injective f.P (nd.g_split k))
    (fun k v v' => not_isConjPl f.P (nd.g_split k) (above_div _ _ v) (above_div _ _ v'))
  have hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  have hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  choose s hs using fun k : Fin 2 => SerInhab.exists_isSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (B.host.g_prime k)
    B.toPre.restRowsFiniteGroupCard_pos ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
        (Finset.mem_univ k)))
  obtain ⟨T₀⟩ : Nonempty (NTypes A) := ⟨TypesInhab.types0 hl hi B.g_cond B.BB_disj tg htg s hs⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨ω, -⟩ := TypesInhab.exists_char (A := MonoidAlgebra ℂ (G0g nd)) 0 one_ne_zero (by simp)
  let eR : G ≃* G0g nd := e₀.trans (grpEquiv N₀.naut A)
  let T : NTypes A := reser (retype T₀ hl hi (fun k => labDat (B.host.g k)) ω) N₀.ntypes
    (fun μ => (a μ).comp (cenPull eR)) (fun μ j => (b μ j).comp (cenPull eR))
  have hT : TypesTrue T f.P f.W :=
    ⟨fun k v => above_div f.P (nd.g_split k) v, fun _ => rfl, fun _ _ _ => rfl, fun k p => h₀.ser k p⟩
  have hco : ∀ g, T.e0.coeff (grpEquiv N₀.naut A g) = N₀.ntypes.e0.coeff g := TypesTrue.typeIdempotent_coeff_across_layers h₀ hT
  have hc : T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g nd)) := goodElement_mem_center_groupAlgebra T
  have hz := ha (cenPull eR ⟨T.e0, hc⟩) fun g => (coeff_cenPull eR _ g).trans (hco (e₀ g))
  have htie : T.IdempotentMatchesAction := by
    refine ⟨fun μ => ?_, fun μ j => ?_⟩
    · rw [NTypes.onAmb, dif_pos hc]
      exact hz.1 μ
    · rw [NTypes.onMt, dif_pos hc]
      exact hz.2 μ j
  have hy : ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := fun x => by
    obtain ⟨g, rfl⟩ := (grpEquiv N₀.naut A).surjective x
    exact ⟨_, (N₀.nStage_trivialCharacter_coeff_eq g).trans (hco g).symm⟩
  choose e hee using hy
  let tw := GaloisStage.nTw B.LL0 nd
  have hT' : IsEmpty tw.Tw := ⟨fun i : Empty => i.elim⟩
  obtain ⟨Y, hY, ⟨th⟩⟩ := exists_nexp_nth_of_isEmpty B C W nd tw hT' e
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := A
    nbc := GaloisStage.nBC A
    nexp := Y
    ntypes := T
    nStage_trivialCharacter_compat := htie
    nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact hee g
    nth := th
    nbr := fun i => hE.elim i
    nbr_ind := fun i => hE.elim i
    self_good := fun i => hE.elim i
    ntwbr := fun i => hT'.elim i
    ntwbr_ind := fun i => hT'.elim i
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i
    etaJ_tie := fun j w _ _ => (heta j w).trans (Finset.sum_eq_zero fun i _ => hE.elim i).symm },
    hE, hT, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem read_unique {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)} {r p : ℕ} (g : ∀ P : S, GL (Fin r) (kP P.1))
    {S' : Finset (Pl E)} (g' : ∀ P : S', GL (Fin r) (kP P.1))
    (hg : ∀ (P : Pl E) (h : P ∈ S) (h' : P ∈ S'), g' ⟨P, h'⟩ = g ⟨P, h⟩) (P : S) (P' : S') (hP : P.1 = P'.1)
    (i : ZMod p ≃+* kP P.1) (i' : ZMod p ≃+* kP P'.1) {x x' : GL (Fin r) (ZMod p)}
    (h : g P = Formalism.UG.bc (i : ZMod p →+* kP P.1) x) (h' : g' P' = Formalism.UG.bc (i' : ZMod p →+* kP P'.1) x') : x = x' := by
  obtain ⟨P, hS⟩ := P
  obtain ⟨P', hS'⟩ := P'
  dsimp only at hP
  subst hP
  rw [hg P hS hS', h, Subsingleton.elim (i' : ZMod p →+* kP P) (i : ZMod p →+* kP P)] at h'
  ext a b
  exact i.injective (congrArg (fun u : GL (Fin r) (kP P) => (u : Matrix (Fin r) (Fin r) (kP P)) a b) h')

theorem e_eq_act {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m : Mat1 K G} {s : Sp1 O φ G} (t : Tie1 σ m s) {e : MonoidAlgebra K G} (h : m.Laws σ e)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (hz : ∀ g, σ (e.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) :
    s.e = s.act z := by
  refine LinearMap.ext_on_range t.forms.span fun i => ?_
  rw [t.forms.op_eq, t.cen z e hz, h.E_eq]

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem exists_bare {K : Ctx} (P : Pre2 K w) :
    ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧
        ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR := by
  letI := P.z.alg
  let e₀ : Gc B w.px ≃* G0g P.Z₀.N.nd := P.z.R.eG.trans P.z.cG
  have hgood : ∀ g, B.embLL ((idemOf P.z.Xg).coeff g) = P.Z₀.N.ntypes.e0.coeff (e₀ g) := P.z.good.2
  obtain ⟨N, hE, hN, hA, hM⟩ := exists_nStage_act P.Z₀.N P.grp (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.q.sha
    (fun _ _ => rfl) e₀ (fun μ => (P.q.p.sA true μ).act) (fun μ j => (P.q.p.sL μ j).act) fun z hz =>
      ⟨fun μ => e_eq_act (P.q.t.tA true μ) (P.q.t.lawsA true μ) z fun g => (hgood g).trans (hz g).symm,
       fun μ j => e_eq_act (P.q.p.tL μ j) (P.q.t.lawsL μ j) z fun g => (hgood g).trans (hz g).symm⟩
  have hpl : ∀ k v, P.Z₀.N.naut.plGw k ((plEquiv P.Z₀.N.naut N.naut k).symm v) = N.naut.plGw k v := fun k v => by
    rw [← TypesTrue.plGw_plEquiv P.grp hN, Equiv.apply_symm_apply]
  refine ⟨N, hE, hN, fun V S G => ⟨?_, fun eR hR => ?_⟩⟩
  · obtain ⟨plg, hp⟩ := P.grpAt.pl
    obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent
      (w.st (RowPk.Over.Z (q := P.q) ⟨_, _, V, S, N, G⟩)).toD7
    refine ⟨⟨(Equiv.sigmaCongrRight fun k => (plEquiv P.Z₀.N.naut N.naut k).symm).trans plg, fun kv => ?_⟩, hi, hc⟩
    exact ⟨(hp ⟨kv.1, _⟩).1.trans (hpl kv.1 kv.2), (hp ⟨kv.1, _⟩).2⟩
  · have he : e₀.trans (grpEquiv P.Z₀.N.naut N.naut) = eR := by
      obtain ⟨plg, iso, h1, h2⟩ := hR
      obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := P.z.pins.keep.grp
      refine MulEquiv.ext fun g => funext fun kv => ?_
      exact (read_unique g (P.z.R.eG g) (P.z.idG g) (plg kv) (plg₀ ⟨kv.1, (plEquiv P.Z₀.N.naut N.naut kv.1).symm kv.2⟩)
        ((h1 kv).trans ((k1 ⟨kv.1, _⟩).trans (hpl kv.1 kv.2)).symm) (iso kv) (iso₀ ⟨kv.1, _⟩) (h2 g kv) (k2 g ⟨kv.1, _⟩)).symm
    subst he
    exact ⟨fun μ z z' hz x => by rw [hA, cenPull_eq _ hz], fun μ j z z' hz x => by rw [hM, cenPull_eq _ hz]⟩

theorem stepW_bare : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w), ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧ ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR :=
  StepW.of_all fun _ _ _ _ _ _ _ _ P => exists_bare P

end GlobalTheory.Mem.R3.Rw.Bare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem below_of_overOne : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  intro D D' hsub v v₁ v₂ h12 hb x x' hxx'
  rw [hb x x' hxx']
  obtain ⟨y, hy, hye⟩ := hsub (x : D.what₂.LL)
  have hyx : y = (x' : D'.what₂.LL) := D'.what₂.embLL.injective (hye.trans hxx')
  have hint : IsIntegral ℤ (⟨(x' : D'.what₂.LL), hyx ▸ hy⟩ : ↥D'.LL0) :=
    (isIntegral_algebraMap_iff (algebraMap ↥D'.LL0 D'.what₂.LL).injective).1 (RingOfIntegers.isIntegral_coe x')
  let z : 𝓞 ↥D'.LL0 := ⟨⟨(x' : D'.what₂.LL), hyx ▸ hy⟩, hint⟩
  have hz : algebraMap (𝓞 ↥D'.LL0) (𝓞 D'.what₂.LL) z = x' := by
    apply RingOfIntegers.ext
    rfl
  rw [← hz, ← GlobalTheory.TwistChoice.val_pos_iff_mem, ← GlobalTheory.TwistChoice.val_pos_iff_mem]
  exact h12 z

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
section
noncomputable section

namespace GlobalTheory.Mem.SRe.StdUnique

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 2000000 in

theorem reads_mem (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k k' : Unit → GA B (B.R.N i)}
    (hR : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y st' k')
    (x : U) (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) : ∃ h : x.1 ∈ U', chi' ⟨x.1, h⟩ = chi x := by
  obtain ⟨c, -⟩ := hR.onto ()
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have h1 : PtOf (y c * k ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR.pt c)
  have h2 : PtOf (y c * k' ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR'.pt c)
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := h1.uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [e]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) hx) hk)
  obtain ⟨q, hq⟩ := ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
  have hq' : PtOf (y c * x.1 * k' ()) q := by
    have e : y c * x.1 * k' () = y c * x.1 * k () * ((y c * k ())⁻¹ * (y c * k' ())) := by group
    rw [e]
    exact PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
  obtain ⟨κ, hgam, hκq, hcos⟩ := (hR.lev c x.1 q hq).1 x.2
  have hm : x.1 ∈ U' := (hR'.lev c x.1 q hq').2 ⟨κ, hgam, hκq, hcos⟩
  refine ⟨hm, Units.ext ?_⟩
  exact (hR'.chr c ⟨x.1, hm⟩ κ hgam (by rw [hκq]; exact hq')).trans (hR.chr c x κ hgam (by rw [hκq]; exact hq)).symm

set_option maxHeartbeats 2000000 in

theorem reads_unique (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    (hR : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k) (hy : y' = y)
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (hU' : U' ≤ UAd B.sp.cm (B.R.N i)) : Lb' = Lb ∧ U' = U ∧ HEq chi' chi := by
  obtain ⟨k, hR⟩ := hR
  obtain ⟨k', hR'⟩ := hR'
  subst hy
  have e : U' = U := le_antisymm (fun x hx => (reads_mem I u i hR' hR ⟨x, hx⟩ (hU' hx)).1)
    fun x hx => (reads_mem I u i hR hR' ⟨x, hx⟩ (hU hx)).1
  subst e
  refine ⟨Submodule.ext fun x => (hR'.lb () x).trans (hR.lb () x).symm, rfl, heq_of_eq (MonoidHom.ext fun x => ?_)⟩
  exact (reads_mem I u i hR hR' x (hU x.2)).2

variable (l : I.Laws)

set_option maxHeartbeats 2000000 in

theorem lev_le (hI : I.Ok) (hP : TC.Pins B X) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m)
    (K : ClsTied (D := I.rec7 l Z) u i hi) : (show Subgroup (GA B (B.R.N i)) from K.lev.U) ≤ UAd B.sp.cm (B.R.N i) := by
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((K.lev.U_eq x).1 hx).1

set_option maxHeartbeats 4000000 in

theorem std_pair (hI : I.Ok) (hP : TC.Pins B X) (Z Z' : TC.Later B (I.cols l)) (u : B.Word) {Ch Ch' : ℕ → Type}
    {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} {chOf' : ∀ i, ((I.rec7 l Z').mem u).C.cls i → Ch' i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (F' : FormsTiedSym (I.rec7 l Z') u Ch' chOf')
    (hF : I.StdF l Z u F) (hF' : I.StdF l Z' u F') :
    F'.to0.cls0.lev.Lb = F.to0.cls0.lev.Lb ∧ F'.to0.cls0.lev.U = F.to0.cls0.lev.U ∧ HEq F'.to0.cls0.lev.chi F.to0.cls0.lev.chi ∧
      F'.to0.cls0.y = F.to0.cls0.y ∧ F'.to0.val0.eY = F.to0.val0.eY := by
  have hy : ∀ c : (I.stp u I.mu0 0).Cl, (F'.to0.cls0.y c).1 = (F.to0.cls0.y c).1 := fun c =>
    (hF'.yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans (hF.yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm
  have h := reads_unique I u 0 (hF.ends 0 (Nat.zero_le _) (Or.inl rfl)) (hF'.ends 0 (Nat.zero_le _) (Or.inl rfl)) (funext hy)
    (lev_le I l hI hP Z u 0 _ _) (lev_le I l hI hP Z' u 0 _ _)
  refine ⟨h.1, h.2.1, h.2.2, funext fun c => Subtype.ext (hy c), Equiv.ext fun z => Subtype.ext ?_⟩
  exact (hF'.eY 0 (Nat.zero_le _) (Or.inl rfl) z).trans (hF.eY 0 (Nat.zero_le _) (Or.inl rfl) z).symm

set_option maxHeartbeats 4000000 in

theorem car_of_same {D : D7} {u : D.what₂.Word} {F₁ F' : Forms0 D u}
    {lev : StepLevel D.host.F D.host.E (sigD D) (gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (badG D)}
    {y : (D.mem u).C.cls 0 → UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {eY : (D.mem u).C.Y 0 ≃ Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)}
    (h : F₁.cls0.lev = lev ∧ F₁.cls0.y = y ∧ F₁.val0.eY = eY)
    (h' : F'.cls0.lev.Lb = lev.Lb ∧ F'.cls0.lev.U = lev.U ∧ HEq F'.cls0.lev.chi lev.chi ∧ F'.cls0.y = y ∧ F'.val0.eY = eY) :
    F'.cls0.lev.Lb = F₁.cls0.lev.Lb ∧ F'.cls0.lev.U = F₁.cls0.lev.U ∧ HEq F'.cls0.lev.chi F₁.cls0.lev.chi ∧
      F'.cls0.y = F₁.cls0.y ∧ F'.val0.eY = F₁.val0.eY := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact h'

set_option maxHeartbeats 4000000 in

theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have h1 := std_pair w.I w.l w.ok w.pins Z (reL Z Zn) u (col.C.forms u) (col'.C.forms u) (col.std u) (col'.std u)
  exact car_of_same (F₁ := F₁ u) (F' := (col'.C.forms u).to0) (lev := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.lev :)))
    (y := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.y :))) (eY := (by with_unfolding_all exact ((col.C.forms u).to0.val0.eY :))) ((by with_unfolding_all exact ((h u) :))) ((by with_unfolding_all exact (h1 :)))

end GlobalTheory.Mem.SRe.StdUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharEqOfOverOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.SatForced

theorem resChar_eq_of_overOne (D : D7) {v v' : D.what₂.places.Pl} (h : GlobalTheory.TwistChoice.OverOne D v v') :
    D.what₂.places.resChar v = D.what₂.places.resChar v' := by
  have hp := D.what₂.places.resChar_prime v
  have h1 := GlobalTheory.TwistChoice.val_resChar_pos D v
  have h2 := (h ((D.what₂.places.resChar v : ℕ) : 𝓞 ↥D.LL0)).1 (by simpa using h1)
  exact GlobalTheory.TwistChoice.eq_resChar_of_pos D v' hp (by simpa using h2)

theorem mem_W1F_of_overOne : ∀ (K : Ctx) (D : D7) (v v' : D.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D v v' →
    v ∈ placesWithNonzeroContentOrConj D (F0K K.s D) → v' ∈ placesWithNonzeroContentOrConj D (F0K K.s D) := by
  intro K D v v' h hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : D.what₂.places.resChar (D.plEq.symm y) = D.what₂.places.resChar v := by
    rcases hy with e | e
    · rw [e, Equiv.symm_apply_apply]
    · rw [e]; exact GlobalTheory.Mem.NonzeroPlacesOverPrimes.resChar_symm_conjPl D v
  refine ⟨j, D.plEq v', Or.inl rfl, ?_⟩
  have e2 : F0K K.s D (D.plEq v') j = F0K K.s D y j := by
    unfold F0K
    rw [key, Equiv.symm_apply_apply, resChar_eq_of_overOne D h]
  rw [e2]; exact hne

end GlobalTheory.Mem.SatForced
end

