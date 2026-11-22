import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrincipalIdealRingWittPowerSeriesAwayPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPrincipalIdealRing_away_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  intro l _ K bk
  have h : (l : bk.S) = C ((l : ℕ) : Wq l bk.a) := (map_natCast C l).symm
  rw [h]
  exact GlobalTheory.ChartRing.isPrincipalIdealRing_away_C (WittVector.irreducible l (k := Fq l bk.a)) _

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet

namespace GlobalTheory.UnivChar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

section Chosen

def IsUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ i Q M, Y.delU i Q M = GalChar.delU D.host X.cc (X.l i) Q M

def withUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => GalChar.delU D.host X.cc (X.l i) Q M
    delU_unr := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).1
    delU_l := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.1
    delU_anti := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.1
    delU_open := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.1
    delU_res := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.1
    delU_conj := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.1 }

end Chosen

section Family

variable (X) in

abbrev Fam (i : X.Tw) (M : ℕ) : Type := PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))

def admitted (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (P : PlE D.host) : Prop :=
  P ∉ S ∧ IsSplitPl D.host P ∧ DecV N P ≤ H

def IsCharOfFam (Y : NExp D.R D.host D.what₂ D.LL0 N X) (H : X.Tw → ℕ → Subgroup (GE N))
    (S : X.Tw → ℕ → Finset (PlE D.host)) (d : ∀ i M, Fam X i M) : Prop :=
  ∀ i M Q, ConjCl (D := D) Q → ∀ (P : PlE D.host) (hP : P ∈ Q),
    (∃ v, Over P v ∧ admitted (H i M) (S i M) v ∧ ∃ s : ℤˣ, ∀ σ, Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ =
      ((s : ℤ) : ZMod (X.l i ^ M)) * Multiplicative.toAdd (d i M v σ)) ∨
    ((∀ v, Over P v → ¬ admitted (H i M) (S i M) v) ∧ ∀ σ, Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 0)

variable {i : X.Tw} {M : ℕ} (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (d : Fam X i M)

open Classical in

def setChar (T : Set (PlE D.host)) : GE N →* Multiplicative (ZMod (X.l i ^ M)) :=
  if h : ∃ v, v ∈ T ∧ admitted H S v then d h.choose else 1

open Classical in

def famCoord (Q : Finset (PlE D.host)) (P : PlE D.host) : GE N →* Multiplicative (ZMod (X.l i ^ M)) :=
  if GalChar.pair D.host P ⊆ ↑Q then setChar H S d (GalChar.pair D.host P) else 1

def famDel (Q : Finset (PlE D.host)) : GE N →* Multiplicative (DelQM D.host (X.l i) Q M) :=
  delAll X i M fun P : ↥Q => famCoord H S d Q P.1

theorem famDel_apply (Q : Finset (PlE D.host)) (σ : GE N) (P : ↥Q) :
    Multiplicative.toAdd (famDel H S d Q σ) P = Multiplicative.toAdd (famCoord H S d Q P.1 σ) := rfl

theorem famDel_eq_one_iff (Q : Finset (PlE D.host)) (σ : GE N) :
    famDel H S d Q σ = 1 ↔ ∀ P ∈ Q, famCoord H S d Q P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem famCoord_of_closed {Q : Finset (PlE D.host)} (hQ : ConjCl (D := D) Q) {P : PlE D.host} (hP : P ∈ Q) :
    famCoord H S d Q P = setChar H S d (GalChar.pair D.host P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

theorem famCoord_conj (Q : Finset (PlE D.host)) {P P' : PlE D.host} (h : IsConjPl D.host P P') :
    famCoord H S d Q P' = famCoord H S d Q P := by
  unfold famCoord
  rw [GalChar.pair_eq h]

theorem setChar_pair (P : PlE D.host) :
    (∃ v, Over P v ∧ admitted H S v ∧ setChar H S d (GalChar.pair D.host P) = d v) ∨
    ((∀ v, Over P v → ¬ admitted H S v) ∧ setChar H S d (GalChar.pair D.host P) = 1) := by
  by_cases h : ∃ v, v ∈ GalChar.pair D.host P ∧ admitted H S v
  · exact Or.inl ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
  · exact Or.inr ⟨fun v hv ha => h ⟨v, hv, ha⟩, dif_neg h⟩

variable {H S d}

theorem famCoord_laws (h : AdmFam X i M H S d) (Q : Finset (PlE D.host)) (P : PlE D.host) :
    IsOpen ((famCoord H S d Q P).ker : Set (GE N)) ∧ AntiHom X.cc (famCoord H S d Q P) ∧
    TrivAbove (famCoord H S d Q P) (X.l i) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A,
      famCoord H S d Q P σ = 1) := by
  have triv : ∀ c : GE N →* Multiplicative (ZMod (X.l i ^ M)), c = 1 →
      IsOpen (c.ker : Set (GE N)) ∧ AntiHom X.cc c ∧ TrivAbove c (X.l i) ∧
      (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, c σ = 1) := by
    rintro _ rfl
    exact ⟨by rw [MonoidHom.ker_one]; exact isOpen_univ, fun _ _ _ => inv_one.symm, fun _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ => rfl⟩
  by_cases hs : GalChar.pair D.host P ⊆ ↑Q
  · have e : famCoord H S d Q P = setChar H S d (GalChar.pair D.host P) := if_pos hs
    rcases setChar_pair H S d P with ⟨v, hv, ha, e'⟩ | ⟨-, e'⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := h.2.2.2 v ha.1 ha.2.1 ha.2.2
      rw [e, e']
      exact ⟨h1, h2, h3, fun w hw => h4 w fun ho => hw (hs (over_trans hv ho))⟩
    · exact triv _ (e.trans e')
  · exact triv _ (if_neg hs)

end Family

section Record

variable {H : X.Tw → ℕ → Subgroup (GE N)} {S : X.Tw → ℕ → Finset (PlE D.host)} {d : ∀ i M, Fam X i M}

def withFam (Y : NExp D.R D.host D.what₂ D.LL0 N X) (h : ∀ i M, AdmFam X i M (H i M) (S i M) (d i M)) :
    NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => famDel (H i M) (S i M) (d i M) Q
    delU_unr := fun i Q M v hv A hA σ hσ =>
      (famDel_eq_one_iff _ _ _ Q σ).2 fun P _ => (famCoord_laws (h i M) Q P).2.2.2 v hv A hA σ hσ
    delU_l := fun i Q M v hv A hA σ hσ =>
      (famDel_eq_one_iff _ _ _ Q σ).2 fun P _ => (famCoord_laws (h i M) Q P).2.2.1 v hv A hA σ hσ
    delU_anti := fun i Q M g g' hg => Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((famCoord_laws (h i M) Q P.1).2.1 g g' hg))
    delU_open := fun i Q M => by
      have e : ((famDel (H i M) (S i M) (d i M) Q).ker : Set (GE N)) =
          ⋂ P ∈ Q, ((famCoord (H i M) (S i M) (d i M) Q P).ker : Set (GE N)) := by
        ext σ
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, famDel_eq_one_iff]
      rw [e]
      exact isOpen_biInter_finset fun P _ => (famCoord_laws (h i M) Q P).1
    delU_res := fun i M Q' Q hs h1 h2 σ P hP => by
      rw [famDel_apply, famDel_apply, famCoord_of_closed _ _ _ h1 hP, famCoord_of_closed _ _ _ h2 (hs hP)]
    delU_conj := fun i Q M P hP P' hP' hc => ⟨1, fun σ => by
      rw [famDel_apply, famDel_apply]
      simp only [famCoord_conj _ _ _ Q hc, Units.val_one, Int.cast_one, one_mul]⟩ }

end Record

theorem delUTie_of_isUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : K1 X → IsUnivChar Y → DelUTie Y :=
  fun hK hY => GalChar.delUTie_of_exists Y hY hK

def withTrivial (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun _ _ _ => 1
    delU_unr := fun _ _ _ _ _ _ _ _ _ => rfl
    delU_l := fun _ _ _ _ _ _ _ _ _ => rfl
    delU_anti := fun _ _ _ _ _ _ => inv_one.symm
    delU_open := fun _ _ _ => by rw [MonoidHom.ker_one]; exact isOpen_univ
    delU_res := fun _ _ _ _ _ _ _ _ _ _ => rfl
    delU_conj := fun _ _ _ _ _ _ _ _ => ⟨1, fun _ => (mul_zero _).symm⟩ }

end GlobalTheory.UnivChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsoLocAppendSingleton
section
noncomputable section

namespace GlobalTheory.LocCongrRoad

open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

private theorem foldr_lpSum_lpTw_lpChar (hL : CharSum N A) {w : PlE H} (x c : A.LP w) (hc : A.lpDim c = 1)
    (s : ℝ) (L : List ℝ) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar x c) (s - k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw x (s - k)) acc) (A.lpZero w)) c := by
  induction L with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) c 0 hc).2.2).symm
  | cons k L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, (hL w _ _ c 0 hc).1, (hL w _ (A.lpZero w) c _ hc).2.1]

theorem spehLoc_twist (hL : CharSum N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpTw_lpChar N A hL (A.locG p.π w) (A.locG χ w) (A.locG_dim χ w) _ _

theorem isoLoc_twist (hL : CharSum N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) (A.locG χ w) 0 hχ).2.2).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [spehLoc_twist N A hL p χ w, ih, (hL w _ _ _ 0 hχ).1]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem main : ∀ (D : D7), CharSum D.nd D.naut → ∀ i : D.nd.Loc, LocCongr D.nd D.naut i := by
  intro D hL i Sig Sig' _ _ h w hw
  rw [isoLoc_twist D.nd D.naut hL, isoLoc_twist D.nd D.naut hL, isoLoc_append_singleton,
    isoLoc_append_singleton, h w hw]

end GlobalTheory.LocCongrRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabCompat
section
open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.LabelCompat

theorem labCompat : ∀ (D : D7) (i : D.nd.Loc), LabCompat D.nd D.naut i := by
  intro D i σ Sig hσ
  have key : ∀ k, D.nd.lab k σ = fun v =>
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
    intro k
    funext v
    rw [D.naut.lab_loc i k σ v, hσ.2.2 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [key k]

end GlobalTheory.LabelCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabels
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.TwistLabel

theorem teich_zero' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

theorem teich_injective' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : Function.Injective t := by
  have h0 := teich_zero' t ht
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  intro x y h
  by_cases hx : x = 0
  · by_contra hxy
    exact hne y (fun hy => hxy (hx.trans hy.symm)) (by rw [← h, hx, h0])
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem prod_scaleRoots {α : Type*} (s : Multiset α) (f : α → ℂ) (c : ℂ) :
    ((s.map fun x => X - C (f x)).prod).scaleRoots c = (s.map fun x => X - C (f x * c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_sub_C_scaleRoots, IH,
      Multiset.map_cons, Multiset.prod_cons]
    rw [leadingCoeff_X_sub_C, one_mul, ne_eq, leadingCoeff_eq_zero]
    exact (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C _).ne_zero

theorem roots_prod_map {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map fun x => X - C (f x)).prod).roots = s.map f := by
  rw [show (s.map fun x => X - C (f x)) = (s.map f).map (fun a => X - C a) by rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

end GlobalTheory.TwistLabel

open GlobalTheory.TwistLabel in
theorem main : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  intro D hT _ hDep hGen k w hw L χ u hL hχ hχl
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ, hG⟩ := hGen
  have hLP := hT.1
  have hγI : γ k w ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := (hγ.2 k w hw).1
  have hdim : D.naut.lpDim (D.naut.lpChar L χ) = D.naut.lpDim L := D.naut.lpDim_char L χ hχ
  have hχdeg : (D.naut.items₂ k w χ).natDegree = D.naut.lpDim χ := by rw [hχl, natDegree_X_sub_C, hχ]
  have hχtame : TameLP D χ := ((hDep k w hw χ).2).1 hχdeg
  have hLtame : TameLP D L := ((hDep k w hw L).2).1 hL
  have hLχtame : TameLP D (D.naut.lpChar L χ) := by
    intro σ hσ hwσ
    have h1 := hχtame σ hσ hwσ
    rw [hχ, pow_one] at h1
    have h2 := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 σ hσ).2 1 (by rw [h1, map_one])
    rw [h2, hLtame σ hσ hwσ, scaleRoots_one, hdim]
  have hfull : (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L := by
    rw [← hdim]; exact ((hDep k w hw _).2).2 hLχtame
  refine ⟨hfull, ?_⟩
  set u' := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) with hu'
  have hrχ : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w χ) = {u'} := by
    rw [hχl, Formalism.CyclotomicNorms.rootsBar, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]
  have hχγ : D.naut.inePol χ (γ k w) = X - C (D.ntypes.teichC k u') := by
    rw [hG k w hw χ hχdeg, hrχ]; simp
  have hsc := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 (γ k w) hγI).2 _ hχγ
  rw [hG k w hw L hL, prod_scaleRoots, hG k w hw _ (hfull.trans hdim.symm)] at hsc
  have hr := congrArg Polynomial.roots hsc
  rw [roots_prod_map, roots_prod_map] at hr
  have hinj := teich_injective' (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  apply Multiset.map_injective hinj
  rw [hr, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp, map_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem mu0_del_tame {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (C.mu0 j * C.delAt l).LevelLe w 1 := by
  have hd : (C.delAt l).TameAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.tame w
    · exact C.isDel.tame w
  exact HChar.LevelLe.mul ((C.isMu0 j).tame w) hd

theorem mu0_del_unr {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ¬ Over4 D.host w) : (C.mu0 j * C.delAt l).UnrAt w := by
  have h1 : ∀ k, ¬ OverP D.host (D.host.g k) w := fun k hk => hw (Or.inl ⟨k, hk⟩)
  have hd : (C.delAt l).UnrAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.unr w (fun h => hw (Or.inr (Or.inr h)))
    · exact C.isDel.unr w (fun h => hw (Or.inr (Or.inl h)))
  exact HChar.UnrAt.mul ((C.isMu0 j).unr w h1) hd

theorem lam0_expAt : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)),
    ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  intro D Z hZ l j a w
  obtain ⟨h4, h0, hO⟩ := expIn_cond0 D.R D.host Z.q0 Z.w0 hZ.places w
  have hA := hZ.aux a
  unfold LamDat.lam0
  by_cases hw : Over4 D.host w
  · rw [h4 hw]
    exact expAt_mul_inv _ (Z.chi a) _ w 2 (by norm_num) (hA.two w hw) (mu0_del_tame Z.C l j w)
  · by_cases hb : below w = below Z.w0
    · rw [(h0 hb).2]
      have hu := mu0_del_unr Z.C l j w hw
      exact expAt_mul_inv _ (Z.chi a) _ w 1 le_rfl (hA.one w hb) ((HChar.unrAt_iff _ _).1 hu)
    · rw [hO hw hb]
      have hu := HChar.UnrAt.mul (mu0_del_unr Z.C l j w hw) (HChar.UnrAt.inv (hA.unr w hw hb))
      intro m
      exact ⟨fun _ => Nat.zero_le m, fun _ => HChar.UnrAt.levelLe hu m⟩

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tate_double_annihilator : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdual S hBS hSZ c hc hann
  obtain ⟨β, hβ0, hβB, -⟩ := GlobalTheory.T.integral_tate_pairing_lattice_dual hT l P K LL O hO L1 hL1 A A' LA LA' m hdual
  haveI : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hT l P K LL O hO A LA
  let e : (LL ⧸ L1.T) ≃ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    Submodule.quotEquivOfEq _ _ hL1
  let β₁ : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    β.compr₂ e.toLinearMap
  have hβ₁ : ∀ d c, β₁ d c = 0 ↔ β d c = 0 := fun d c => by
    simp only [β₁, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    exact e.map_eq_zero_iff
  have hker : (latticeCoboundaries LA).comap (latticeCocycles LA).subtype ≤ LinearMap.ker β₁ := by
    intro d hd
    rw [LinearMap.mem_ker]
    ext c
    exact (hβ₁ d c).2 (hβB d c hd)
  let β₂ : LatticeCohomology LA →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype).liftQ β₁ hker
  have hβ₂ : ∀ d c, β₂ (Submodule.Quotient.mk d) c = β₁ d c := fun d c => rfl
  have key := GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers l LL O hO (LatticeCohomology LA) ↥(divisibleCocycles LA') β₂ (S.comap (divisibleCocycles LA').subtype) ?_
    ⟨c, hc⟩ ?_
  · exact key
  · intro c' hc'
    show c'.1 ∈ S
    apply hBS
    apply GlobalTheory.T.lattice_dual_pairing_cyclotomic hT l P K LL O hO L1 hL1 A A' LA LA' m hdual c'.1 c'.2
    intro d hd
    have h := hc' (Submodule.Quotient.mk ⟨d, hd⟩)
    rw [hβ₂, hβ₁] at h
    exact (hβ0 ⟨d, hd⟩ c').1 h
  · intro d hd
    induction d using Submodule.Quotient.induction_on with
    | _ d0 =>
    rw [hβ₂, hβ₁]
    apply (hβ0 d0 ⟨c, hc⟩).2
    apply hann d0.1 d0.2
    intro s hs
    have h := hd ⟨s, hSZ hs⟩ hs
    rw [hβ₂, hβ₁] at h
    exact (hβ0 d0 ⟨s, hSZ hs⟩).1 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgreeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengths_modulo_submodule_agree : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  first | exact @GlobalTheory.LenModAgree.main | exact GlobalTheory.LenModAgree.main | (intros; apply GlobalTheory.LenModAgree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumnStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_restrictionLattice_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | exact GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | (intros; apply GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModulesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_finite_discrete_modules : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (M' : Type) [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M'] [Finite M'] (ρ : Representation k (G F Ω) M) (ρ' : Representation k (G F Ω) M') (χ : G F Ω → k) (P : M →ₗ[k] M' →ₗ[k] k), ContAction ρ → ContAction ρ' → (∀ g, χ g = (((cycMod F Ω l 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k)) → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) → ∀ (L : ∀ v, Submodule k (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (L' : ∀ v, Submodule k (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ v ∉ S, L' v = Formalism.GaloisCohomology.unrAt ρ' (A.1 v)) → (∀ v ∈ S, ∀ y : Z1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk y ∈ L' v ↔ ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupCob (fun g : Dec (F := F) (A.1 v) => χ g.1) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P x.1 y.1) → Finite (Formalism.GaloisCohomology.SelAll ρ A L) ∧ Finite (Formalism.GaloisCohomology.SelAll ρ' A L') ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Formalism.GaloisCohomology.SelAll ρ' A L') * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.DualPairFormula.greenbergWiles_dualPair | exact GlobalTheory.DualPairFormula.greenbergWiles_dualPair | (intros; apply GlobalTheory.DualPairFormula.greenbergWiles_dualPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldIntegerIffAlgebraicClosureNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (x : L), (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  first | exact @GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt | exact GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt | (intros; apply GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixComputesTwistedSelmerResidualTransferStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixComputesTwistedSelmer_residual_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k], ((X.l i : ℕ) : k) = 0 → Function.Surjective (algebraMap (X.O0 i) k) → ∀ aug : abelian₂ X i M ι →ₐ[X.O0 i] k, (∀ δ, aug (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) = 1) → ∃ E : LinearMap.ker (Φ.map aug).mulVecLin →ₗ[k] H1 (red i k (Tgl i s)), Function.Injective E ∧ (∀ x, E x ∈ selOn bkP i (Tgl i s) (1 : GE N →* kˣ) k Q) ∧ ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (th : abelian₂ X i M ι →ₐ[X.O0 i] B), ((X.l i : ℕ) : B) = 0 → ∀ x : Fin a → B, (Φ.map th).mulVec x = 0 → ∃ z : GE N → Fin D.R.r → B, IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + th ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • ((Tmat i s g).map (algebraMap (X.O0 i) B)).mulVec (z h)) ∧ ∀ f : B →+ k, (∀ y b, f (th y * b) = aug y * f b) → ∃ (x' : LinearMap.ker (Φ.map aug).mulVecLin) (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = f (x c)) ∧ (∀ g c, z'.1 g c = f (z g c)) ∧ E x' = cl z' := by
  first | exact @GlobalTheory.ResSel.Transfer.computes_transfer | exact GlobalTheory.ResSel.Transfer.computes_transfer | (intros; apply GlobalTheory.ResSel.Transfer.computes_transfer <;> assumption)
end

