import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_weightSizes_eventually_along_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.LowRow.weightSizes_along | exact GlobalTheory.LowRow.weightSizes_along | (intros; apply GlobalTheory.LowRow.weightSizes_along <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def placeAlg (E : Place (algebraMap ℂ K)) : Subalgebra ℂ K :=
  { E.ring.toSubring with algebraMap_mem' := E.const_mem }

theorem mem_placeAlg {E : Place (algebraMap ℂ K)} {e : K} : e ∈ placeAlg E ↔ e ∈ E.ring :=
  Iff.rfl

variable (κ') in

def tensMap (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' →ₐ[ℂ] K ⊗[ℂ] κ' :=
  Algebra.TensorProduct.map A.val (AlgHom.id ℂ κ')

theorem tensMap_injective (A : Subalgebra ℂ K) : Function.Injective (tensMap κ' A) := by
  have e : ⇑(tensMap κ' A) = ⇑(LinearMap.rTensor κ' A.val.toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  rw [e]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

def tens (A : Subalgebra ℂ K) : Subalgebra ℂ (K ⊗[ℂ] κ') := (tensMap κ' A).range

def tensEquiv (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') A :=
  AlgEquiv.ofInjective _ (tensMap_injective A)

@[simp] theorem coe_tensEquiv (A : Subalgebra ℂ K) (w : A ⊗[ℂ] κ') :
    (tensEquiv A w : K ⊗[ℂ] κ') = tensMap κ' A w := rfl

theorem tmul_mem {A : Subalgebra ℂ K} {e : K} (he : e ∈ A) (b : κ') :
    e ⊗ₜ[ℂ] b ∈ tens (κ' := κ') A :=
  ⟨⟨e, he⟩ ⊗ₜ b, rfl⟩

variable {κ : Type} [Field κ] [Algebra ℂ κ]

def graphIdeal (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') :
    Ideal (tens (κ' := κ') (placeAlg E)) :=
  Ideal.span ({b | ∃ e : K, 0 < E.ord e ∧ (b : K ⊗[ℂ] κ') = e ⊗ₜ 1} ∪
    {b | ∃ a : R, (b : K ⊗[ℂ] κ') = (a : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)})

def gens (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ')
    (hR : E.Contains R) (t : E.ring) {k : ℕ} (z : Fin k → R) :
    Fin (k + 1) → tens (κ' := κ') (placeAlg E) :=
  Fin.cons ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩ fun i =>
    ⟨(z i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (z i)),
      sub_mem (tmul_mem (hR _ (z i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩

variable {L : Type} [Field L] [Algebra (K ⊗[ℂ] κ') L]

theorem one_notMem {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [h𝔭 : 𝔭.IsPrime] :
    (1 : tens (κ' := κ') A) ∉ 𝔭 :=
  (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top

def locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] : Subring L where
  carrier := {x | ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧
    x * algebraMap (K ⊗[ℂ] κ') L s = algebraMap (K ⊗[ℂ] κ') L a}
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * a', s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, map_mul]
    rw [← hx, ← hy]
    ring
  one_mem' := ⟨1, 1, one_notMem 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * s' + a' * s, s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, map_mul, map_add]
    rw [← hx, ← hy]
    ring
  zero_mem' := ⟨0, 1, one_notMem 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    simp only [Subalgebra.coe_neg, map_neg]
    rw [← hx]
    ring

def toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    tens (κ' := κ') A →+* locAt (L := L) 𝔭 where
  toFun b := ⟨algebraMap (K ⊗[ℂ] κ') L b, b, 1, one_notMem 𝔭, by simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (b : tens (κ' := κ') A) : (toQ (L := L) 𝔭 b : L) = algebraMap (K ⊗[ℂ] κ') L b := rfl

theorem exists_mul_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (x : locAt (L := L) 𝔭) : ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧ x * toQ 𝔭 s = toQ 𝔭 a := by
  obtain ⟨x, a, s, hs, hx⟩ := x
  exact ⟨a, s, hs, Subtype.ext hx⟩

section Inj

variable {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
  (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
include hinj

theorem algebraMap_ne_zero {b : tens (κ' := κ') A} (hb : b ≠ 0) :
    algebraMap (K ⊗[ℂ] κ') L b ≠ 0 := fun h =>
  hb (Subtype.ext (hinj (h.trans (map_zero _).symm)))

theorem isUnit_toQ {b : tens (κ' := κ') A} (hb : b ∉ 𝔭) : IsUnit (toQ (L := L) 𝔭 b) := by
  have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
    algebraMap_ne_zero hinj fun h => hb (h ▸ 𝔭.zero_mem)
  refine IsUnit.of_mul_eq_one (b := ⟨(algebraMap (K ⊗[ℂ] κ') L b)⁻¹, 1, b, hb, by simp [hb0]⟩)
    (Subtype.ext ?_)
  simp [hb0]

theorem isLocalRing_locAt : IsLocalRing (locAt (L := L) 𝔭) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
  by_cases ha : a ∈ 𝔭
  · right
    have hsa : s - a ∉ 𝔭 := fun h => hs (by simpa using add_mem h ha)
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [sub_mul, one_mul, hx, ← map_sub]
    exact isUnit_toQ 𝔭 hinj hsa
  · left
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [hx]
    exact isUnit_toQ 𝔭 hinj ha

theorem isUnit_toQ_iff {b : tens (κ' := κ') A} : IsUnit (toQ (L := L) 𝔭 b) ↔ b ∉ 𝔭 := by
  refine ⟨fun h hb => ?_, isUnit_toQ 𝔭 hinj⟩
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 y
  have e2 : toQ (L := L) 𝔭 (b * a) = toQ 𝔭 s := by
    rw [map_mul, ← e, ← mul_assoc, hy, one_mul]
  have e3 : b * a = s := Subtype.ext (hinj (congrArg Subtype.val e2))
  exact hs (e3 ▸ 𝔭.mul_mem_right a hb)

theorem toQ_mem_maximalIdeal_iff [IsLocalRing (locAt (L := L) 𝔭)] {b : tens (κ' := κ') A} :
    toQ (L := L) 𝔭 b ∈ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ↔ b ∈ 𝔭 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_toQ_iff 𝔭 hinj, not_not]

theorem map_le_maximalIdeal [IsLocalRing (locAt (L := L) 𝔭)] :
    𝔭.map (toQ (L := L) 𝔭) ≤ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) :=
  Ideal.map_le_iff_le_comap.2 fun _ hb => (toQ_mem_maximalIdeal_iff 𝔭 hinj).2 hb

end Inj

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem torsion_exhaust_geometric : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  intro hL R _ _ _ P N hN1 hNu C b hb hgen K _ _ x p hp
  have hNu' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hNu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨hfin, -, -, het, hcard⟩ := hL.mulN (Spec (CommRingCat.of R)) P N hN1
  have : Etale (mulA P.A N).left := het hNu'
  have : IsSeparated (mulA P.A N).left := inferInstance
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ≫ mulA P.A N = y ^ N := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of R))}, (1 : Z ⟶ P.A).left = Z.hom ≫ η[P.A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let Kk : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.snd (mulA P.A N).left η[P.A].left)
  have hη : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  let i : Kk ⟶ P.A := Over.homMk (pullback.fst (mulA P.A N).left η[P.A].left) (by
    change pullback.fst (mulA P.A N).left η[P.A].left ≫ P.A.hom = pullback.snd (mulA P.A N).left η[P.A].left
    rw [← Over.w (mulA P.A N), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hlift : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ^ N = 1 → ∃ l : Z ⟶ Kk, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA P.A N).left = Z.hom ≫ η[P.A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over (Spec (CommRingCat.of R))} (l l' : Z ⟶ Kk), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  have : Etale Kk.hom := inferInstanceAs (Etale (pullback.snd (mulA P.A N).left η[P.A].left))
  have : IsSeparated Kk.hom := inferInstanceAs (IsSeparated (pullback.snd (mulA P.A N).left η[P.A].left))

  have inj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R))
      (σ τ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A), σ ^ N = 1 → τ ^ N = 1 →
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ τ → σ = τ := by
    intro F _ y σ τ hσ hτ e
    obtain ⟨ls, rfl⟩ := hlift σ hσ
    obtain ⟨lt, rfl⟩ := hlift τ hτ
    have e' : toUnit (Over.mk y) ≫ ls = toUnit (Over.mk y) ≫ lt := hmono _ _ (by simpa using e)
    have hu : (toUnit (Over.mk y)).left = y := by
      simpa using Over.w (toUnit (Over.mk y))
    have : ConnectedSpace (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of R)))
    have key : ls.left = lt.left := by
      refine GlobalTheory.eq_of_connected_of_unramified_of_point Kk.hom
        ((Over.w ls).trans (Over.w lt).symm) y ?_
      have h2 := congr(($e').left)
      rw [Over.comp_left, Over.comp_left, hu] at h2
      exact h2
    rw [Over.OverMorphism.ext key]
  have natK : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), (N : F) ≠ 0 :=
    fun y => by simpa using (hNu.map (Spec.preimage y).hom).ne_zero
  let T0 := {σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A // σ ∈ Set.range b}
  have tor : ∀ σ : T0, σ.1 ^ N = 1 := fun σ => by obtain ⟨c, hc⟩ := σ.2; rw [← hc]; exact hb c
  let res : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      T0 → {q : Over.mk y ⟶ P.A // q ^ N = 1} := fun y σ =>
    ⟨toUnit _ ≫ σ.1, by rw [← MonObj.comp_pow, tor σ, MonObj.comp_one]⟩
  have resInj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      Function.Injective (res y) := fun y σ τ e =>
    Subtype.ext (inj y σ.1 τ.1 (tor σ) (tor τ) (congrArg Subtype.val e))
  let Ω := AlgebraicClosure (FractionRing R)
  have c0 := hcard Ω (TF (R := R) Ω).hom (natK (TF (R := R) Ω).hom)
  have cx := hcard K x (natK x)
  have hpos : N ^ (2 * P.g) ≠ 0 := pow_ne_zero _ (by omega)
  have : Finite {q : Over.mk (TF (R := R) Ω).hom ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (c0 ▸ hpos)
  have : Finite {q : Over.mk x ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (cx ▸ hpos)
  have bij0 : Function.Bijective (res (TF (R := R) Ω).hom) := by
    refine ⟨resInj _, fun q => ?_⟩
    obtain ⟨c, hc⟩ := hgen q.1 q.2
    exact ⟨⟨b c, c, rfl⟩, Subtype.ext hc.symm⟩
  have cT : Nat.card T0 = N ^ (2 * P.g) := (Nat.card_eq_of_bijective _ bij0).trans c0
  have bijx := (Nat.bijective_iff_injective_and_card (res x)).2 ⟨resInj x, cT.trans cx.symm⟩
  obtain ⟨⟨σ, c, rfl⟩, hσ⟩ := bijx.2 ⟨p, hp⟩
  exact ⟨c, (congrArg Subtype.val hσ).symm⟩

end GlobalTheory.Poinc.Tors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem zCo_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hch : GlobalTheory.FockCompare.Chart θ σ) {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (z : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) =
      fun τ => (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ := by
  funext τ
  have e : compAt θ τ (GlobalTheory.FockCompare.iotaW σ T S z) = Matrix.of (z τ) := congrFun (hch.pi_iota T S z) τ
  simp only [GlobalTheory.FockPos.zCo, e]
  rfl

theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ * GlobalTheory.FockPos.frAt fr τ = 1 ∧ GlobalTheory.FockPos.frAt fr τ * (GlobalTheory.FockPos.frAt fr τ)⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ)),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ))⟩

theorem coord_back {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹) *
      GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) := by
  have h1 := (frAt_inv frS τ).1
  have h2 := (frAt_inv frT τ).1
  calc _ = ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * GlobalTheory.FockPos.frAt frT τ) * Matrix.of (Z τ) *
        ((GlobalTheory.FockPos.frAt frS τ)⁻¹ * GlobalTheory.FockPos.frAt frS τ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ThetaLawOF

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem trace_conjTranspose_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (Aᴴ * B).trace = ∑ a, ∑ b, starRingEnd ℂ (A a b) * B a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (x y : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.VacUnique.omO S T x y = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (y τ) * GlobalTheory.FockPos.frAt frS τ) a b) *
        ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (x τ) * GlobalTheory.FockPos.frAt frS τ) a b)).re := by
  rw [GlobalTheory.VacUnique.omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (Matrix.of (x τ)) (Matrix.of (y τ))).re = _
  rw [GlobalTheory.FockJetOrigin.hAt_coord (BS := fun τ => GlobalTheory.FockPos.frAt frS τ)
    (BT := fun τ => GlobalTheory.FockPos.frAt frT τ) (GlobalTheory.FockPos.frAt_on frS hS τ) (GlobalTheory.FockPos.frAt_on frT hT τ),
    trace_conjTranspose_mul, GlobalTheory.FockJetOrigin.realPlace_cmTrace_zero_element_eq_I_mul_abs, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]

theorem torusHermitianForm_scaled_coordinate_eq {N N' : ℕ} {δ : ℂ} (hδ : δ ≠ 0) (Z X : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b) := by
  have e : (∑ τ, ∑ i, ∑ j, (δ • Z) τ i j * starRingEnd ℂ ((δ • X) τ i j)) =
      (δ * starRingEnd ℂ δ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ).abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ := rfl
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, e, hL, GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot, hxi, Complex.mul_conj]
  have h0 : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ).ne'
  have h1 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0)
  have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.sqrt D.host.d ≠ 0)
  push_cast
  field_simp

theorem al_mul_self {N N' : ℕ} (T0 : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.al D T0 x * Formalism.MainNotions.TaylorLogMetric.al D T0 x = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.al, ← mul_zpow, show (-1 : ℂ) * -1 = 1 by norm_num, _root_.one_zpow]

theorem entry (zz xx : ℂ) (r : ℝ) :
    (Real.pi : ℂ) * Complex.I * ((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ zz * xx)).re : ℝ) : ℂ) -
      2 * (Real.pi : ℂ) * (r : ℂ) * (zz * starRingEnd ℂ xx) - (Real.pi : ℂ) * (r : ℂ) * (xx * starRingEnd ℂ xx) =
      (Real.pi : ℂ) * (r : ℂ) * ((‖zz‖ ^ 2 : ℝ) - (‖zz + xx‖ ^ 2 : ℝ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

end GlobalTheory.ThetaLawOF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LaStdEntries

open Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7}

def entSub (D : D7) (a b : ℕ) (S : Submodule (𝓞 D.host.E) D.host.E) :
    Submodule (𝓞 D.host.E) (Matrix (Fin b) (Fin a) D.host.E) where
  carrier := {A | ∀ i j, A i j ∈ S}
  add_mem' hA hB i j := by simpa using S.add_mem (hA i j) (hB i j)
  zero_mem' i j := by simp
  smul_mem' o A hA i j := by simpa using S.smul_mem o (hA i j)

theorem mem_entSub {a b : ℕ} {S : Submodule (𝓞 D.host.E) D.host.E}
    {A : Matrix (Fin b) (Fin a) D.host.E} : A ∈ entSub D a b S ↔ ∀ i j, A i j ∈ S := Iff.rfl

theorem homL_le {a b : ℕ} :
    homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) ≤ entSub D a b 1 := by
  refine Submodule.span_le.mpr ?_
  intro A hA i j
  have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
    simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
    intro k
    by_cases hk : k = j
    · subst hk; simp [Submodule.one_eq_range]
    · simp [Pi.single_apply, hk]
  have h := hA _ hj
  simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  have := h i
  simpa [Matrix.mulVec_single] using this

theorem YYl_le {a b : ℕ} :
    YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b)
      ≤ entSub D a b (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  refine Submodule.span_le.mpr ?_
  rintro B ⟨x, hx, A, hA, rfl⟩ i j
  obtain ⟨o, ho⟩ := (Submodule.mem_one).1 (homL_le hA i j)
  show x * A i j ∈ _
  rw [← ho, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ o hx

theorem K_mul_mem_AA {c : 𝓞 D.host.K} (hc : c ∈ D.host.ccK) {x : D.host.E}
    (hx : x ∈ D.host.AA0) : ((c : D.host.K) : D.host.E) * x ∈ D.host.AA := by
  show _ ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
  refine FractionalIdeal.mul_mem_mul ?_ hx
  rw [FractionalIdeal.mem_coeIdeal]
  exact ⟨_, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem La_std_rep : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b),
    x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) →
    ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧
      x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  intro D δ a b x hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D D.host.ccK δ w hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ?_⟩
    · simpa using K_mul_mem_AA hc (YYl_le hA i j)
    · rw [GlobalTheory.MomSetup.embV_smulK, smul_smul]
  | zero => exact ⟨0, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).zero_mem, by rw [GlobalTheory.MomSetup.embV_zero, smul_zero]⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨A, hA, rfl⟩ := h1
    obtain ⟨B, hB, rfl⟩ := h2
    exact ⟨A + B, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).add_mem (hA i j) (hB i j),
      by rw [GlobalTheory.MomSetup.embV_add, smul_add]⟩
  | neg x _ h =>
    obtain ⟨A, hA, rfl⟩ := h
    exact ⟨-A, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hA i j), by rw [GlobalTheory.MomSetup.embV_neg, smul_neg]⟩

end GlobalTheory.LaStdEntries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
section
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial

namespace GlobalTheory.NablaFin

theorem totalDegree_le_of_colW {O : Type} [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ weightedHomogeneousSubmodule O (Formalism.GradedWeylDivisibility.colW N N) ν) :
    f.totalDegree ≤ ∑ t, ν t := by
  rw [mem_weightedHomogeneousSubmodule] at hf
  unfold totalDegree
  refine Finset.sup_le fun s hs => ?_
  have hw := hf (mem_support_iff.1 hs)
  rw [← hw, Finsupp.weight_apply]
  refine le_of_eq ?_
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem dualWeyl_finite (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ν : Fin N → ℕ) :
    Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := by
  have hle : Formalism.GradedWeylDivisibility.dualWeyl O N N ν ≤ restrictTotalDegree (Fin N × Fin N) O (∑ t, ν t) := by
    intro f hf
    rw [mem_restrictTotalDegree]
    exact totalDegree_le_of_colW N ν f (by unfold Formalism.GradedWeylDivisibility.dualWeyl at hf; exact hf.1)
  haveI : IsNoetherian O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := isNoetherian_of_le hle
  infer_instance

theorem nablaT_finite : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ι : Type) [Fintype ι]
    (lam : ι → ℕ → ℕ), Module.Finite O (NablaT O N lam) := by
  intro O _ _ N ι _ lam
  haveI : ∀ τ, Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_finite O N _
  exact PiTensorProduct.finite

end GlobalTheory.NablaFin
end

