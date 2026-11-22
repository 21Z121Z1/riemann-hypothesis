import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.Columns.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.LevLiftPt

theorem isPtOf_mul_fr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g m : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (hg : IsPtOf hc g p)
    (hm : m ∈ Formalism.L2.Herm.UstdAf hc n) (h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (h2 : ∀ i j, ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (hT : ∀ P ∈ ST, ∀ i j, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F P (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j))
    {h : GLG E n SG} (hh : ∀ w : SG, LevRead.IsRed w.1 m (h w)) (c : GLQ E n Q)
    (hfr : ∀ (P : Q) (i j : Fin n), adAt F P.1 (((g * m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((p.fr P * ((c P)⁻¹ : GLint E n P.1).1) (Pi.single j 1) i)) :
    IsPtOf hc (g * m⁻¹) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  have hg0 : IsPtOf hc g (ChTwRead.noFr p) :=
    ⟨hg.uni, hg.lat, hg.f, hg.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  have H := LevRead.isPtOf_mul (Q := ∅) (fun P => Finset.notMem_empty P) hg0 hm h1 h2 hT hh
    (fun P => absurd P.2 (Finset.notMem_empty _))
  refine ⟨H.uni, H.lat, H.f, H.be, fun P i j => ?_⟩
  rw [hfr P i j]
  rfl

theorem int_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E :=
  GlobalTheory.T.supported_unitary_adelic_integral_with_inverse

theorem vT_notOver : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' :=
  GlobalTheory.T.levelPrime_primes_not_over_bad_prime_place

theorem isRed_of_red : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)), ∀ g ∈ Formalism.L2.Col.GLint E n P, ∀ (A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)), (∀ y ∈ Formalism.L2.Col.stdAt E n P, redV P (g y) = A.mulVec (redV P y)) → ∀ (m : GL (Fin n) (AfE F E)), (∀ r s, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → LevRead.IsRed P m A := by
  intro F E _ _ _ _ _ _ n P g hg A hA m hm r s
  have h := ReadBad.isRed_ratA (F := F) hg hA r s
  have e : adAt F P (((GlobalTheory.TwU.ratA F (toGLm E n g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s) := by
    show adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) _) = _
    rw [adAt_inclE]
    rfl
  show HasRes P _ _
  rw [hm r s, ← e]
  exact h

theorem adAt_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}
    {u : GL (Fin n) (AfE F E)} {v : HeightOneSpectrum (𝓞 F)} (hoff : ∀ v', v' ≠ v → bc (prV (E := E) v') u = 1)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Formalism.L2.Col.IsOver v Q) (i j : Fin n) :
    adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have hne : Q.under (𝓞 F) ≠ v := by
    rintro rfl
    exact hQ rfl
  refine ChTwRead.adAt_congr_prV Q ?_
  have h1 := congrArg (fun g : GL (Fin n) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => g.val i j) (hoff _ hne)
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => g.val i j)
    (map_one (bc (prV (E := E) (Q.under (𝓞 F)))) : bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) = 1)
  exact h1.trans h2.symm

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g0 x kk : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (hp : IsPtOf hc g0 p) (hx : x ∈ Formalism.L2.Herm.UstdAf hc n) (hk : kk ∈ Formalism.L2.Herm.UstdAf hc n)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v P)
    (hxoff : ∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) (g' : Sp E n ≃ₗ[E] Sp E n) (hg' : g' ∈ Formalism.L2.Col.GLint E n P)
    (hpt : ∀ r s, adAt F P (((kk⁻¹ * x * kk : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g'.toLinearMap r s))
    (hST : ∀ P' ∈ ST, ¬ Formalism.L2.Col.IsOver v P') (hover : ∀ w, w ∈ SG ∨ w ∈ Q → Formalism.L2.Col.IsOver v w → w = P)
    (h : GLG E n SG) (c : GLQ E n Q)
    (hG : ∀ hP : P ∈ SG, ∀ y ∈ Formalism.L2.Col.stdAt E n P, redV P (g' y) = ((h ⟨P, hP⟩)⁻¹).1.mulVec (redV P y))
    (hGo : ∀ w : SG, w.1 ≠ P → ∀ y ∈ Formalism.L2.Col.stdAt E n w.1,
      redV w.1 ((1 : Sp E n ≃ₗ[E] Sp E n) y) = ((h w)⁻¹).1.mulVec (redV w.1 y))
    (hQ : ∀ hP : P ∈ Q, g' = ((c ⟨P, hP⟩)⁻¹).1)
    (hQo : ∀ P'' : Q, P''.1 ≠ P → (1 : Sp E n ≃ₗ[E] Sp E n) = ((c P'')⁻¹).1) :
    IsPtOf hc (g0 * (kk⁻¹ * x * kk)) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  set m := kk⁻¹ * x * kk with hm
  have hmU : m ∈ Formalism.L2.Herm.UstdAf hc n := mul_mem (mul_mem (inv_mem hk) hx) hk
  have hmoff : ∀ v', v' ≠ v → bc (prV (E := E) v') m = 1 := fun v' hv' => by
    rw [hm, map_mul, map_mul, map_inv, hxoff v' hv', mul_one, inv_mul_cancel]
  have hmioff : ∀ v', v' ≠ v → bc (prV (E := E) v') m⁻¹ = 1 := fun v' hv' => by
    rw [map_inv, hmoff v' hv', inv_one]
  have hInt := int_of_split hc m hmU v P hv hmoff g' hg' hpt
  have e : g0 * m = g0 * m⁻¹⁻¹ := by rw [inv_inv]
  rw [e]
  refine isPtOf_mul_fr hp (inv_mem hmU) (fun r s => (hInt r s).2) (fun r s => by rw [inv_inv]; exact (hInt r s).1) ?_ ?_ c ?_
  · intro P' hP' r s
    exact adAt_of_off hmioff (hST P' hP') r s
  · intro w
    by_cases hw : w.1 = P
    · obtain ⟨w, hwm⟩ := w
      simp only at hw
      subst hw
      have hC := isRed_of_red w g' hg' _ (hG hwm) m hpt
      obtain ⟨Bm, hB⟩ := LevRead.exists_isRed (x := m⁻¹) (P := w)
        (fun r s => (mem_rInt_iff F E _).1 (hInt r s).2 w)
        (fun r s => by rw [inv_inv]; exact (mem_rInt_iff F E _).1 (hInt r s).1 w)
      have h1 := hC.mul hB
      rw [mul_inv_cancel] at h1
      have h2 := h1.unique LevRead.isRed_one
      have h3 : (h ⟨w, hwm⟩)⁻¹ * Bm = 1 := Units.ext (by rw [Units.val_mul]; exact h2)
      rw [inv_mul_eq_one] at h3
      rw [h3]
      exact hB
    · have hwnot : ¬ Formalism.L2.Col.IsOver v w.1 := fun h' => hw (hover w.1 (Or.inl w.2) h')
      have hC1 := isRed_of_red (F := F) w.1 1 (one_mem _) _ (hGo w hw) (1 : GL (Fin n) (AfE F E)) (fun r s => by
        rw [show LinearMap.toMatrix' (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1 from LinearMap.toMatrix'_id]
        simp only [Units.val_one, Matrix.one_apply]
        split_ifs <;> simp)
      have h2 := hC1.unique LevRead.isRed_one
      have h3 : (h w)⁻¹ = 1 := Units.ext h2
      rw [inv_eq_one] at h3
      rw [h3]
      intro r s
      rw [adAt_of_off hmioff hwnot r s]
      exact LevRead.isRed_one r s
  · intro P'' r s
    rw [inv_inv, Units.val_mul, Matrix.mul_apply, map_sum]
    by_cases hPP : P''.1 = P
    · obtain ⟨P'', hPm⟩ := P''
      simp only at hPP
      subst hPP
      rw [← hQ hPm]
      simp_rw [map_mul, hp.fr ⟨P'', hPm⟩ r, hpt, ← map_mul]
      rw [← map_sum]
      congr 1
      rw [LinearEquiv.mul_apply]
      conv_rhs => rw [pi_eq_sum_univ (g' (Pi.single s 1)), map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix'_apply,
        LinearEquiv.coe_coe]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
      congr 2
      exact congrArg (fun y => p.fr ⟨P'', hPm⟩ y r) (by funext j; simp [Pi.single_apply, eq_comm])
    · have hPnot : ¬ Formalism.L2.Col.IsOver v P''.1 := fun h' => hPP (hover P''.1 (Or.inr P''.2) h')
      rw [← hQo P'' hPP, mul_one]
      simp_rw [map_mul, adAt_of_off hmoff hPnot]
      simp only [Units.val_one, Matrix.one_apply, apply_ite (adAt F P''.1), map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hp.fr P'' r s

theorem mul_conj {G : Type} [Group G] (y x k : G) : y * k * (k⁻¹ * x * k) = y * x * k := by group

set_option maxHeartbeats 1000000 in

theorem pt_of_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))), kk = k (chOf c) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x = 1) → ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, (∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * x * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s)) → ∀ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) → LiftsInv I κ' P g' → (∀ P', P' ≠ P → LiftsInv I κ' P' 1) → PtOf (((K (chOf c)).y ⟨c, rfl⟩).1 * x * kk) (((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv x hx hxoff g' hg' hpt κ' hK hLP hLo
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext y
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 y
  rw [hseam] at hv hpt
  obtain ⟨hLev, hdisj, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj
  have hp := IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  rw [← hkk] at hp

  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : kk ∈ UAd B.sp.cm (B.R.N i) := hkk ▸ hpk.uni
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have hxU : x ∈ UAd B.sp.cm (B.R.N i) := by
    have e : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
        UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
    exact e ▸ hx
  have hγ : κ'.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ'.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hK.1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  have hq : ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 =
      ((1, fun w => (κ'.2.1.1 w), κ'.2.2.1) : UF B.fields.E (B.R.N i) × GLG B.fields.E (B.R.N i) (B.primes X).vGs × GLQ B.fields.E (B.R.N i) (I.Q a)) • ((I.stp u a i).rep c).1.1 := by
    show FrmG.incl _ _ κ' • _ = _
    rw [← hγ]
    rfl

  have hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    have h := P.2
    simp only [uSG, Finset.mem_union] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ColIn.Q_subset_SQ I a h)
  have hS : ∀ w, w ∈ (B.primes X).vGs ∨ w ∈ I.Q a → w ∈ SBof I a := by
    intro w hw
    show w ∈ uSG _ _
    simp only [uSG, Finset.mem_union]
    exact hw
  have key := core B.sp.cm hp hxU hk v P.1 hv hxoff g' hg' hpt (vT_notOver I hOk a P v hv u) (fun w hw hwv => by
      have hw' : w ∈ uSG (B.primes X).vGs I.SQ := by
        simp only [uSG, Finset.mem_union]
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (ColIn.Q_subset_SQ I a h)
      rcases rll_over_cases B.sp.cm hv hwv with h | h
      · exact h
      · exact absurd (h ▸ hw') (hLev.split P.1 hPu))
    (fun w => κ'.2.1.1 w) κ'.2.2.1 hLP.2.1
    (fun w hw => (hLo ⟨w.1, hS w.1 (Or.inl w.2)⟩ (fun e => hw (congrArg Subtype.val e))).2.1 w.2)
    hLP.2.2
    (fun P'' hP'' => (hLo ⟨P''.1, hS P''.1 (Or.inr P''.2)⟩ (fun e => hP'' (congrArg Subtype.val e))).2.2 P''.2)
  have e := mul_conj (G := GA B (B.R.N i)) ((K (chOf c)).y ⟨c, rfl⟩).1 x kk
  rw [hq]
  exact e ▸ key

end GlobalTheory.Mem.Col2.LevLiftPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.R3.Rw.rr_eta_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((v))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((Xo)) := by
  intro B C a b G _ _ Pl0 I0 T Ks _ _ iK A3 R F
  letI := alg b iK
  refine ⟨fun j v => ?_, fun y y' bb E jE jE' n c Xo hj h => ?_⟩
  · tr_via (fun X : Cx.CxData A3.fam3.amb3 => (open Classical in
        if hj : 1 ≤ j ∧ j ≤ a.D.R.m then
          if a.D.plEq (((v :))) ∈ R.twPl then
            A3.A.fam.etaJ F.P0 F.ψ0 (A3.fam3.toSub2 X.zs) ⟨j - 1, by omega⟩ (R.mu (a.D.plEq (((v :))))) (a.D.plEq (((v :))))
          else 0
        else 0) = etaOf R F j ((by with_unfolding_all exact (v :)))) (toCx3_eq b R F) (Eq.refl (etaOf R F j ((by with_unfolding_all exact (v :)))))
  · have e : jE' = jE := eq_of_heq hj
    subst jE'
    tr_via (fun u : Parts R => ∃ h : n = ((cxW R F u).data F.cr bb).D,
      (∀ x : Fin n → a.D.what₂.LL, jE (∑ i, a.D.what₂.embLL (x i) • c i) =
        PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A3.A.v0) (E := R.HE.H)
          ((by with_unfolding_all exact (((cxW R F u).iC F.cr bb A3.A.μ0 (cpt A3.A.v0.embedding (x ∘ Fin.cast h.symm))) :)))))) ∧
      ∀ v, Xo v = (((cxW R F u).data F.cr bb).XE v).submatrix (Fin.cast h) (Fin.cast h) ∧ IsUnit (Xo v).det) (parts_eq b R F) h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTransla
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Forms

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
  (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet Xf.E n ST SG)) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem eqFun_smul_grp (φ : (Formalism.L2.Col.formGSD C Λ).EqFun) (u : Λ.grp) (a : Formalism.L2.Col.GLG Xf.E n SG)
    (d : Formalism.L2.Col.DecoSet Xf.E n ST SG) :
    (φ : Formalism.L2.Col.DecoSet Xf.E n ST SG → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG) * a) • d) =
      ((Λ.chr u : Xf.Kˣ) : Xf.K) • (φ : Formalism.L2.Col.DecoSet Xf.E n ST SG → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) := by
  have e := φ.2 ((1, u) : Formalism.L2.Col.FormG Λ) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d)
  have e' : ((1, u) : Formalism.L2.Col.FormG Λ) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) =
      ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG) * a) • d := by
    show ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG)) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) = _
    rw [smul_smul, Prod.mk_mul_mk, one_mul]
  rw [e'] at e
  rw [e]
  show ((Λ.chr u : Xf.Kˣ) : Xf.K) • C.rho 1 _ = _
  rw [map_one]
  rfl

end Forms

theorem semilin_inv_smul {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (m : V →ₛₗ[σ] W) (k : K) (c : ℂˣ) (hk : σ k = c) (x : V) :
    m x = ((c⁻¹ : ℂˣ) : ℂ) • m (k • x) := by
  rw [LinearMap.map_smulₛₗ, hk, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.Mem.R3.RowAct

namespace GlobalTheory.Mem.R3.RowAct

theorem act_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hRD
  refine ⟨{
      red := eG.symm.toMonoidHom.comp (rTupQ X.toD7.sp.X' L.βX (L.datXt t))
      red_surj := ?_
      red_ker := ?_
      act_eq := ?_ }, ?_⟩
  · intro g
    have key := GlobalTheory.Mem.R3.FlagOnto.exists_flag_rTup X px I hX U L hI hV hL t (eG g)
    obtain ⟨q, hq⟩ := key
    refine ⟨q, ?_⟩
    have e : rTupQ X.toD7.sp.X' L.βX (L.datXt t) q = eG g := hq
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = g
    rw [e, MulEquiv.symm_apply_apply]
  · intro q
    have e := rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) q
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff eG.symm).trans e
  · intro g κ hκ f
    obtain ⟨m, hm⟩ := hRD
    obtain ⟨u, hdeco, hch⟩ := GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation X px I hX U L eG hI hV hL hG t κ
    have hg : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf X.toD7.sp.X') : GL _ _))) = g := hκ
    rw [hg] at hdeco
    funext h
    have e1 := hm ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) h
    have e2 := hm f (h * (κ : Bridge.Gf X.toD7.sp.X'))
    refine e1.trans ?_
    refine Eq.trans ?_ (congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • v) e2).symm
    have e3 : ((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm
        ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) = Formalism.L2.Col.g0HatRepEqFunX X.B.wts I.Ch I.sel t.1 g
          (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f) :=
      LinearEquiv.symm_apply_apply _ _
    have e4 := eqFun_smul_grp _ _ (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f)
      u (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g)⁻¹ (RowAd.decoAd X I t h)
    refine (congrArg (fun ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).EqFun =>
      m ((ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D → (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).V)
        (RowAd.decoAd X I t h))) e3).trans ?_
    refine (semilin_inv_smul m _ _ hch _).trans ?_
    refine congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • m v) ?_
    exact e4.symm.trans (congrArg _ (hdeco h).symm)
  · intro q
    have e : eG (eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q)) = rTupQ X.toD7.sp.X' L.βX (L.datXt t) q :=
      MulEquiv.apply_symm_apply _ _
    exact e

end GlobalTheory.Mem.R3.RowAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparisonStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowIdentifications_realRowSide_of_chainComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | exact GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | (intros; apply GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowPartFormsAndNonzeroVectorsEveryPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RowsLift

theorem rows_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH hM hg p hp i
  have hA := GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp
  have hB : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ := by
    intro h0
    apply hA
    rw [← Submodule.finrank_eq_zero, ← hH.prim.dimParts i p, h0, finrank_bot]
  refine ⟨?_, fun v hv => ?_⟩
  · intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    have : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ R.Wp3 i p := hw.1
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).2 this
  · obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp i hB
    exact ⟨x, hx, GlobalTheory.T.base_level_frames_hermitian_ne_zero_off_place D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg i v hv x hx0⟩

end GlobalTheory.RowsLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

def St.rowsAre {P : Pre2 K w} (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) :
    R3.RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0 :=
  ⟨x.m.z, x.m.intersectionNumber_baseChange, x.r.Y, x.r.Z.full fun j v h1 h2 => (x.m.eta j v).symm ▸ hη j v h1 h2, fun t => by
    change x.r.Y.tup t = _
    rw [x.r.tup]; exact x.m.tup t⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChan
section
noncomputable section

open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

theorem of_heq_cast {α β : Sort _} {y : β} {x : α} (P : α → Prop) (h : HEq y x) (hx : P x) :
    P (cast (type_eq_of_heq h) y) := by
  cases h
  exact hx

set_option maxHeartbeats 4000000 in

theorem sAtL_exists_ofDiv : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  intro B C a G' _ _ Pl0 T A Ks _ _ iK R F F0 eE s N hh F₁ hS
  have hF : FinX (reY (New.ofDiv a.D N hh) s.P.Y) := finX_reY a.D (New.ofDiv a.D N hh) s.P.X s.P.Y s.P.fin
  have h : SameForms0LevelsAndValues (New.ofDiv a.D N hh) F0 ((by with_unfolding_all exact (F₁ :))) := hS
  obtain ⟨S', hj⟩ := SRest.exists_re_ofDiv N hh s.S h hF
  have hsee := mvSee a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.t s.see
  have hev := mvEv_holds a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.P.G s.t s.c s.ev
  have hrow := mvRowJ a (New.ofDiv a.D N hh) R s.P.X s.P.inst s.P.G s.t eE s.S.j s.rowJ
  letI := alg (reL a (New.ofDiv a.D N hh)) iK
  have hrow' := of_heq_cast (fun j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC s.P.X s.P.G =>
      RowJ (real (reL a (New.ofDiv a.D N hh)) R) (eL a (New.ofDiv a.D N hh) R eE) (XL a (New.ofDiv a.D N hh) s.P.X)
        (hL a (New.ofDiv a.D N hh) s.P.inst) (gdL a (New.ofDiv a.D N hh) s.P.G) (tL a (New.ofDiv a.D N hh) s.t)
        (jL a (New.ofDiv a.D N hh) j)) hj hrow
  let s' : SAt (real (reL a (New.ofDiv a.D N hh)) R) (face (reL a (New.ofDiv a.D N hh)) F) (eL a (New.ofDiv a.D N hh) R eE) F₁ :=
    { P := (by with_unfolding_all exact (s.P.re (New.ofDiv a.D N hh) h hF :))
      S := (by with_unfolding_all exact (S' :))
      t := tL a (New.ofDiv a.D N hh) s.t
      c := s.c
      c_pos := s.c_pos
      see := (by with_unfolding_all exact (hsee :))
      ev := (by with_unfolding_all exact (hev :))
      rowJ := (by with_unfolding_all exact (hrow' :)) }
  exact ⟨s', (by with_unfolding_all exact (Eq.refl (tL a (New.ofDiv a.D N hh) s.t) :))⟩

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRootStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_character_eq_prod_additive_characters_root_alt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ (ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → Fin D.R.r → (ZMod (D.host.g kv.1))ˣ), (∀ kv, ψ' kv ≠ 1) ∧ ∀ k ∈ X.K2, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) → star (X.chi2 k) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root | exact GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root | (intros; apply GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root <;> assumption)
end

