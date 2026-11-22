import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRham
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyPullbackSecond
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetBCGen

section Coeff

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Type} [Fintype I] {n : ℕ}

theorem repr_algebraMap (J : JetRing R I n) (r : R) (ν : Idx I n) :
    J.b.repr (algebraMap R J.B r) ν = if (⟨0, by simp⟩ : Idx I n) = ν then r else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

open scoped Classical in

theorem repr_t_eq_ite_single (J : JetRing R I n) (i : I) (ν : Idx I n) :
    J.b.repr (J.t i) ν = if (⟨Pi.single i 1, by simp⟩ : Idx I n) = ν then 1 else 0 := by
  rw [JetRing.t, J.b.repr_self, Finsupp.single_apply]

variable (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
  (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν))
include hτ

theorem map_algebraMap (r : R) : τ (algebraMap R J.B r) = algebraMap R' J'.B (σ r) :=
  J'.b.ext_elem fun ν ↦ by rw [hτ, repr_algebraMap, repr_algebraMap]; split_ifs <;> simp

theorem map_t (i : I) : τ (J.t i) = J'.t i :=
  J'.b.ext_elem fun ν ↦ by rw [hτ, repr_t_eq_ite_single, repr_t_eq_ite_single]; split_ifs <;> simp

theorem map_π (x : J.B) : J'.π (τ x) = σ (J.π x) := by rw [J'.π_eq, J.π_eq, hτ]

end Coeff

section Crys

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {S S' : Scheme.{0}} {I : Ideal R}
  {I' : Ideal R'} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'}
  {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

theorem ext_of_isBC (hm : m.IsBC) {d d' : Crys κ' t' A'} (h : ∀ c, d (m.pull c) = d' (m.pull c)) :
    d = d' := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

end Crys

section Jet

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type}
  [Fintype I] {n : ℕ} (J : JetRing R I n) {X : Obj F 𝔠 (Sp R)}
  {m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))}
  (hm : m.IsBC) (N : I → Module.End R (HdR X.A))

def jet (x : HdR X.A) : Crys J.κ (spMap J.π) X.A :=
  hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x)

theorem isJetElt_jet (x : HdR X.A) : IsJetElt J X N m x (jet J hm N x) := fun c ↦ by
  have e : ∀ y, hm.bcMap y (m.pull c) = algebraMap R J.B (y c) := fun y ↦ (hm.corr_iff.2 rfl) c
  simp only [jet, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, e]

theorem eq_jet_of_isJetElt {x : HdR X.A} {d : Crys J.κ (spMap J.π) X.A} (h : IsJetElt J X N m x d) :
    d = jet J hm N x :=
  ext_of_isBC hm fun c ↦ (h c).trans (isJetElt_jet J hm N x c).symm

theorem jet_add (x y : HdR X.A) : jet J hm N (x + y) = jet J hm N x + jet J hm N y := by
  simp only [jet, map_add, smul_add, Finset.sum_add_distrib]
  abel

theorem jet_smul (r : R) (x : HdR X.A) : jet J hm N (r • x) = algebraMap R J.B r • jet J hm N x := by
  simp only [jet, map_smul, LinearMap.map_smulₛₗ, smul_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

end Jet

def compMulti {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {M L : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup L] [Module B L] {K : Type} (δ : L [⋀^K]→ₗ[B] B) (Λ : M → L)
    (hadd : ∀ a b, Λ (a + b) = Λ a + Λ b) (hsmul : ∀ (r : R) a, Λ (r • a) = algebraMap R B r • Λ a) :
    MultilinearMap R (fun _ : K ↦ M) B where
  toFun x := δ (fun j ↦ Λ (x j))
  map_update_add' x j a b := by
    have e : ∀ y, (fun k ↦ Λ (Function.update x j y k)) = Function.update (fun k ↦ Λ (x k)) j (Λ y) :=
      fun y ↦ funext fun k ↦ Function.apply_update (fun _ ↦ Λ) x j y k
    simp only [e, hadd, δ.map_update_add]
  map_update_smul' x j r a := by
    have e : ∀ y, (fun k ↦ Λ (Function.update x j y k)) = Function.update (fun k ↦ Λ (x k)) j (Λ y) :=
      fun y ↦ funext fun k ↦ Function.apply_update (fun _ ↦ Λ) x j y k
    simp only [e, hsmul, δ.map_update_smul, smul_eq_mul, Algebra.smul_def]

end GlobalTheory.JetBCGen

namespace GlobalTheory.JetBCGen

theorem detGen_baseChange : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ (δ₁ : X₁.DetGen), Obj.DetCorr σ p δ₀.1 δ₁.1 → ∀ (δ' : Z'.DetGen), Obj.DetCorr τ q Y.δ'.1 δ'.1 →
    ∀ (x : Fin (Module.finrank ℚ F) → HdR X₁.A) (d : Fin (Module.finrank ℚ F) → Crys J'.κ (spMap J'.π) X₁.A)
      (v : Fin (Module.finrank ℚ F) → X₁.Lie) (v' : Fin (Module.finrank ℚ F) → Z'.Lie),
      (∀ j, IsJetElt J' X₁ N₁ mor' (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧
        IsLieImage (crysToDR J'.κ hi'.grp (d j)) (v' j).hom) →
      δ'.1 v' = algebraMap R' J'.B (δ₁.1 v) := by
  intro H F _ _ 𝔠 R R' _ _ σ I _ n J J' X₀ δ₀ N Y X₁ N₁ p hp m hN τ hτ hτdp Z' q hq i' hi' hcomm mor' δ₁
    hδ₁ δ' hδ' x d v v' hx
  classical
  have hBC' : mor'.IsBC := GlobalTheory.T.jet_morphism_is_base_change H J' X₁ mor'
  have hBC0 : Y.mor.IsBC := GlobalTheory.T.jet_morphism_is_base_change H J X₀ Y.mor
  have L₁ : LieExact X₁.A := (H.2.1 R' X₁.A _ X₁.ab X₁.dim).1
  have L₀ : LieExact X₀.A := (H.2.1 R X₀.A _ X₀.ab X₀.dim).1
  have LY : LieExact Y.X'.A := (H.2.1 J.B Y.X'.A _ Y.X'.ab Y.X'.dim).1
  have LZ : LieExact Z'.A := (H.2.1 J'.B Z'.A _ Z'.ab Z'.dim).1
  have hτa := map_algebraMap σ J J' τ hτ
  have hτt := map_t σ J J' τ hτ
  have hbase : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext y
    exact (map_π σ J J' τ hτ y).symm
  have M : GrpMor J.κ (spMap J.π) X₀.A J'.κ (spMap J'.π) X₁.A τ (spMap σ) p :=
    GrpMor.of_isGrpPullback hτdp hbase hp.grp
  have nq : GrpMor (dp0 J.B) (𝟙 _) Y.X'.A (dp0 J'.B) (𝟙 _) Z'.A τ (spMap τ) q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) hq.grp
  have K := Y.mor.comp M
  have key : ∀ c₀, M.pull (Y.mor.pull c₀) = mor'.pull (m.pull c₀) := fun c₀ ↦
    (GrpMor.pull_pull Y.mor M K (fun _ ↦ rfl) rfl c₀).trans
      (GrpMor.pull_pull m mor' K (fun r ↦ (hτa r).symm) (by simp) c₀).symm

  have hM : ∀ x₀ y, m.Corr x₀ y → M.Corr (jet J hBC0 N x₀) (jet J' hBC' N₁ y) := by
    intro x₀ y hy c
    obtain ⟨z, rfl⟩ := hBC0.2 c
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b c₀ =>
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, key,
        isJetElt_jet J' hBC' N₁ y (m.pull c₀), isJetElt_jet J hBC0 N x₀ c₀]
      have e : ∀ i, N₁ i y (m.pull c₀) = σ (N i x₀ c₀) := fun i ↦ hN i x₀ y hy c₀
      simp only [e, hy c₀, map_add, map_sum, map_mul, hτa, hτt]

  let Λ : HdR X₁.A → Z'.Lie := fun y ↦ LZ.toLie Z'.rm (crysToDR J'.κ hi'.grp (jet J' hBC' N₁ y))
  have hΛadd : ∀ a b, Λ (a + b) = Λ a + Λ b := fun a b ↦ by
    simp only [Λ, jet_add, map_add]
  have hΛsmul : ∀ (r : R') a, Λ (r • a) = algebraMap R' J'.B r • Λ a := fun r a ↦ by
    simp only [Λ, jet_smul, map_smul]
  let Φ₁ := compMulti δ'.1 Λ hΛadd hΛsmul
  let Φ₂ : MultilinearMap R' (fun _ : Fin (Module.finrank ℚ F) ↦ HdR X₁.A) J'.B :=
    (Algebra.linearMap R' J'.B).compMultilinearMap
      (δ₁.1.toMultilinearMap.compLinearMap fun _ ↦ L₁.toLie X₁.rm)
  have hΦ : Φ₁ = Φ₂ := by
    obtain ⟨hspan, -, -⟩ := GlobalTheory.T.lie_filtration_spanned_correspondence H σ hp m
    refine MultilinearMap.ext_of_span_eq_top
      (g := fun (_ : Fin (Module.finrank ℚ F)) (y : {y : HdR X₁.A // ∃ y₀, m.Corr y₀ y}) ↦ y.1)
      (fun _ ↦ ?_) fun s ↦ ?_
    · change Submodule.span R' (Set.range Subtype.val) = ⊤
      rw [Subtype.range_coe_subtype]
      exact hspan
    choose x₀ hx₀ using fun j ↦ (s j).2
    let v₀ := fun j ↦ L₀.toLie X₀.rm (x₀ j)
    let w := fun j ↦ LY.toLie Y.X'.rm (crysToDR J.κ Y.pull.grp (jet J hBC0 N (x₀ j)))
    have hgen := Y.gen x₀ (fun j ↦ jet J hBC0 N (x₀ j)) v₀ w fun j ↦
      ⟨isJetElt_jet J hBC0 N (x₀ j), (L₀.toLie_eq_iff _).1 rfl, (LY.toLie_eq_iff _).1 rfl⟩
    have hl₁ : ∀ j, Obj.LieCorr σ p (v₀ j) (L₁.toLie X₁.rm (s j).1) := fun j ↦
      GlobalTheory.T.lie_image_correspondence H σ hp m (hx₀ j) ((L₀.toLie_eq_iff _).1 rfl) ((L₁.toLie_eq_iff _).1 rfl)
    have hlZ : ∀ j, Obj.LieCorr τ q (w j) (Λ (s j).1) := fun j ↦
      GlobalTheory.T.lie_image_correspondence H τ hq nq (crysToDR_corr J.κ Y.pull.grp hi'.grp M nq hcomm (hM _ _ (hx₀ j)))
        ((LY.toLie_eq_iff _).1 rfl) ((LZ.toLie_eq_iff _).1 rfl)
    change δ'.1 (fun j ↦ Λ (s j).1) = algebraMap R' J'.B (δ₁.1 fun j ↦ L₁.toLie X₁.rm (s j).1)
    rw [hδ' w _ hlZ, hgen, hτa, hδ₁ v₀ _ hl₁]
  have hv' : v' = fun j ↦ Λ (x j) := funext fun j ↦
    ((LZ.toLie_eq_iff Z'.rm).2 (by rw [← eq_jet_of_isJetElt J' hBC' N₁ (hx j).1]; exact (hx j).2.2)).symm
  have hv : v = fun j ↦ L₁.toLie X₁.rm (x j) := funext fun j ↦ ((L₁.toLie_eq_iff X₁.rm).2 (hx j).2.1).symm
  subst hv hv'
  exact DFunLike.congr_fun hΦ x

end GlobalTheory.JetBCGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismCompatibleNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_morphism_compatible_nilpotent : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (a : 𝓞 F), ∀ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, act J.κ (spMap J.π) X.rm a d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  first | exact @GlobalTheory.LatJet.jetFil_act_stable | exact GlobalTheory.LatJet.jetFil_act_stable | (intros; apply GlobalTheory.LatJet.jetFil_act_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniquenessStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_morphism_uniqueness : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (c : 𝔠.elt) (φ : Crys J.κ (spMap J.π) X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A →ₗ[J.B] J.B),
        GlobalTheory.AbDual.IsCorrForm J.κ (spMap J.π) X.A X.A (X.P c) φ → ∀ a ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, ∀ b ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, φ a b = 0 := by
  first | exact @GlobalTheory.JetIsotropic.jetFil_isotropic | exact GlobalTheory.JetIsotropic.jetFil_isotropic | (intros; apply GlobalTheory.JetIsotropic.jetFil_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetZetaOfDeRham
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.LatJet GlobalTheory.LatJet.An GlobalTheory.LatJet.An.Det
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An.ZetaNonvanishing₂

theorem mem_Fil_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (H : LieExact A) {x : HdR A}
    {w : Fin g → ℂ} (h : ∃ v, IsLieImage x v ∧ u.IsDiff w v) : x ∈ Fil A ↔ w = 0 := by
  obtain ⟨v, h1, h2⟩ := h
  refine ⟨fun hx ↦ ?_, fun hw ↦ ?_⟩
  · obtain rfl : v = 1 := (H.1 x).unique h1 (isLieImage_one_iff.2 hx)
    exact ArchMetricCompare.eq_zero_of_isDiff u h2
  · obtain rfl : v = 1 := (ArchMetricCompare.isDiff_ne_iff u h1.1 h2).1 hw
    exact isLieImage_one_iff.1 h1

theorem vec_unique {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (H : LieExact A) {x : HdR A}
    {w w' : Fin g → ℂ} (h : ∃ v, IsLieImage x v ∧ u.IsDiff w v) (h' : ∃ v, IsLieImage x v ∧ u.IsDiff w' v) : w = w' := by
  have key := exists_lie_comb u (fun _ : Bool ↦ x) (fun b ↦ if b then w else w') (fun b ↦ by cases b <;> simpa)
    (Finsupp.single true 1 - Finsupp.single false 1)
  simp only [map_sub, Finsupp.linearCombination_single, one_smul, sub_self, if_true, Bool.false_eq_true, if_false] at key
  exact sub_eq_zero.1 ((mem_Fil_iff u H key).1 (zero_mem _))

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ}

theorem pair_special {L : Set E} (T : CxPt 𝔠 φ L) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P)
    (c d : T.U.u.Λ →₀ ℂ) : T.ψ (Finsupp.linearCombination ℂ P c) (Finsupp.linearCombination ℂ P d) =
      ((ε : ℤ) : ℂ) * Real.pi * ∑ a, T.U.h (T.U.e a) * (hol _ c a * ahol _ d a - ahol _ c a * hol _ d a) := by
  obtain ⟨χ, hχ⟩ := T.U.ah
  rw [pair_comb _ P T.ψ (fun a ↦ T.U.h (T.U.e a)) _ (hP.2.2.2.2 _ χ T.ψ hχ T.pol) c d]
  congr 1
  field_simp

theorem exists_comb_eigen [IsCMField E] (H : GlobalTheory.Published.AbelianDeRham) (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y)) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) (i : I) :
    ∃ d, Finsupp.linearCombination ℂ P d = T.y i ∧ hol _ d = Pi.single (T.U.e.symm i) (T.w i) ∧ ahol _ d = 0 := by
  obtain ⟨d, hd⟩ : T.y i ∈ LinearMap.range (Finsupp.linearCombination ℂ P) := by
    rw [Finsupp.range_linearCombination, hP.1]; trivial
  refine ⟨d, hd, vec_unique T.U.u (H.2.1 ℂ T.X.A _ T.X.ab T.X.dim).1 (hd ▸ exists_lie_comb T.U.u P _ hP.2.2.1 d) (T.cm i).2,
    funext fun m ↦ ?_⟩
  obtain ⟨a, h1, h2⟩ := exists_comb _ T.U.u.full (Pi.single m 1)
  have h0 : T.ψ (Finsupp.linearCombination ℂ P a) (T.y i) = 0 := by
    have e : (1 : ℂ) • (T.ψ (Finsupp.linearCombination ℂ P a) (T.y i) • T.y i) = 0 :=
      low_eq_zero hφ hc { T with s := fun _ ↦ 1 } hP h1 h2 i
    rw [one_smul] at e
    rcases smul_eq_zero.1 e with e | e
    · exact e
    · rw [e, map_zero]
  obtain ⟨χ, hχ⟩ := T.U.ah
  have hh : (T.U.h (T.U.e m) : ℂ) ≠ 0 := fun e ↦ by
    have := hχ.2.1 (Pi.single m 1) (by simp)
    simp [Matrix.mulVec_diagonal, e] at this
  rw [← hd, pair_special T hP] at h0
  simp only [h1, h2, Pi.zero_apply, zero_mul, sub_zero, Pi.single_apply, ite_mul, _root_.one_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
  simpa [hh, Real.pi_ne_zero] using h0

theorem low_anti [IsCMField E] (H : GlobalTheory.Published.AbelianDeRham) (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y)) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) (i : I)
    {b : T.U.u.Λ →₀ ℂ} (h1 : hol _ b = 0) (h2 : ahol _ b = Pi.single (T.U.e.symm i) 1) :
    ∃ d, hol _ d = Pi.single (T.U.e.symm i) (-(((ε : ℤ) : ℂ) * T.A i)) ∧ ahol _ d = 0 ∧
      ∀ k, T.low k (Finsupp.linearCombination ℂ P b) = if k = i then Finsupp.linearCombination ℂ P d else 0 := by
  have key : ∀ k, T.low k (Finsupp.linearCombination ℂ P b) =
      (if k = i then -(((ε : ℤ) : ℂ) * Real.pi * T.U.h i * T.s i * T.w i) else 0) • T.y k := fun k ↦ by
    obtain ⟨d, e0, e1, e2⟩ := exists_comb_eigen H hφ hc T hP k
    have e := pair_special T hP b d
    rw [e0] at e
    change T.s k • (T.ψ _ (T.y k) • T.y k) = _
    rw [e, smul_smul]
    congr 1
    simp only [h1, h2, e1, Pi.zero_apply, zero_mul, zero_sub, Pi.single_apply, ite_mul, _root_.one_mul, mul_neg, mul_ite, mul_zero,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hk : k = i
    · subst hk
      simp only [if_true]
      ring
    · simp [hk, Ne.symm hk]
  obtain ⟨d, e0, e1, e2⟩ := exists_comb_eigen H hφ hc T hP i
  refine ⟨(-(((ε : ℤ) : ℂ) * Real.pi * T.U.h i * T.s i * T.w i)) • d, ?_, by rw [map_smul, e2, smul_zero], fun k ↦ ?_⟩
  · rw [map_smul, e1, ← Pi.single_smul, smul_eq_mul, CxPt.A]
    congr 1
    ring
  · rw [key]
    split_ifs with hk
    · rw [map_smul, e0, hk]
    · exact zero_smul _ _

theorem exists_comb_anti {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (w : Fin g → ℂ) :
    ∃ c, hol Λ c = 0 ∧ ahol Λ c = w := by
  obtain ⟨c, h1, h2⟩ := exists_comb Λ h (star w)
  have k : ∀ c : Λ →₀ ℂ, ∃ c', hol Λ c' = star (ahol Λ c) ∧ ahol Λ c' = star (hol Λ c) := fun c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add c d hc hd =>
      obtain ⟨c', e1, e2⟩ := hc
      obtain ⟨d', e3, e4⟩ := hd
      exact ⟨c' + d', by simp only [map_add, e1, e3, star_add], by simp only [map_add, e2, e4, star_add]⟩
    | single x r => exact ⟨Finsupp.single x (star r), by simp, by simp⟩
  obtain ⟨c', e1, e2⟩ := k c
  exact ⟨c', by rw [e1, h2, star_zero], by rw [e2, h1, star_star]⟩

theorem isUnit_jet (hC : JetCalc) {n : ℕ} (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    IsUnit (jet J f) := by
  have e : J.π (jet J f) = f 0 := by
    rw [J.π_eq]
    exact (hC I n J).1 f hf _ [] fun _ ↦ rfl
  have hm : jet J f - algebraMap ℂ J.B (f 0) ∈ RingHom.ker J.π := by
    rw [RingHom.mem_ker, map_sub, e, J.π_algebraMap, sub_self]
  obtain ⟨N, hN⟩ := J.nil.exists_dpow_eq_zero
  have hn : IsNilpotent (jet J f - algebraMap ℂ J.B (f 0)) :=
    ⟨N, by rw [← J.κ.factorial_mul_dpow_eq_pow hm, hN N le_rfl, mul_zero]⟩
  simpa using hn.isUnit_add_right_of_commute ((Ne.isUnit h0).map (algebraMap ℂ J.B)) (Commute.all _ _)

section Main

variable {n : ℕ} {L : Set E} {T : CxPt 𝔠 φ L} {J : JetRing ℂ I n} {Y : Family J T.X T.δ T.low} {G : Germ Y} {ε : ℤˣ}

def period (K : Coord ε G) (c : T.U.u.Λ →₀ ℂ) (ω : primDR G.X.A) (z : I → ℂ) : ℂ :=
  Finsupp.linearCombination ℂ (K.P z) c ((K.mor z).pull ω)

theorem mem_Fil_fibre (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) (c : T.U.u.Λ →₀ ℂ) :
    Finsupp.linearCombination ℂ (K.P z) c ∈ Fil (K.X z).A ↔ ∀ a, hol _ c a + K.ζ z (T.U.e a) * ahol _ c a = 0 := by
  rw [mem_Fil_iff (K.U z hz).u (H.2.1 ℂ (K.X z).A _ (K.X z).ab (K.X z).dim).1
    (exists_lie_comb (K.U z hz).u (K.P z) _ (K.lie z hz) c), funext_iff]
  refine forall_congr' fun a ↦ Eq.congr_left ?_
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    RCLike.star_def, mul_add, Finset.sum_add_distrib, mul_left_comm _ (K.ζ z _), ← Finset.mul_sum]

theorem period_eq (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) {c d : T.U.u.Λ →₀ ℂ} {r : ℂ}
    (h : ∀ a, hol _ c a + K.ζ z (T.U.e a) * ahol _ c a = r * (hol _ d a + K.ζ z (T.U.e a) * ahol _ d a))
    {ω : primDR G.X.A} (hω : ω ∈ PrimitiveSubmodule G.X.A) : period K c ω z = r * period K d ω z := by
  have e := (mem_Fil_fibre H K hz (c - r • d)).2 fun a ↦ by
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h a
  have e' := (Submodule.mem_dualAnnihilator _).1 e ((K.mor z).pull ω) ((K.mor z).isMor.pullback1_mem_hodgeFiltration hω)
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at e'
  exact sub_eq_zero.1 e'

theorem exists_period_ne_zero (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) {c : T.U.u.Λ →₀ ℂ}
    {a : Fin (Module.finrank ℚ (FR E))} (h : hol _ c a + K.ζ z (T.U.e a) * ahol _ c a ≠ 0) :
    ∃ ω ∈ PrimitiveSubmodule G.X.A, period K c ω z ≠ 0 := by
  by_contra hh
  push_neg at hh
  refine h ((mem_Fil_fibre H K hz c).1 ?_ a)
  letI : Algebra G.B ℂ := (G.y z : G.B →+* ℂ).toAlgebra
  have e := (H.2.2.1 G.B G.X.A _ G.X.ab G.X.dim ℂ (K.X z).A (K.q z) (K.pull z).grp).2
  refine (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_
  rw [e] at hw
  refine (Submodule.span_le (p := LinearMap.ker (Finsupp.linearCombination ℂ (K.P z) c))).2 ?_ hw
  rintro _ ⟨ω, hω, rfl⟩
  exact hh ω hω

theorem hasJet_period (hC : JetCalc) (K : Coord ε G) (hb : Y.mor.IsBC)
    (m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q)
    (c : T.U.u.Λ →₀ ℂ) (ω : primDR G.X.A) : HasJet J (period K c ω)
      (crysToDR J.κ Y.pull.grp (hb.bcMap (Finsupp.linearCombination ℂ K.P₀ c)) (m'.pull ω)) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    have e : period K 0 ω = fun _ ↦ 0 := funext fun z ↦ by simp only [period, map_zero, LinearMap.zero_apply]
    simpa only [e, map_zero, LinearMap.zero_apply] using hasJet_const (J := J) 0
  | add c d hc hd =>
    have e : period K (c + d) ω = fun z ↦ period K c ω z + period K d ω z :=
      funext fun z ↦ by simp only [period, map_add, LinearMap.add_apply]
    simpa only [e, map_add, LinearMap.add_apply] using hc.add hC hd
  | single x r =>
    have e : period K (Finsupp.single x r) ω = fun z ↦ r * K.P z x ((K.mor z).pull ω) :=
      funext fun z ↦ by simp only [period, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_eq_mul]
    rw [e, Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact (hasJet_const r).mul hC ⟨SCV.analyticAt_of_differentiableOn (K.P_hol x ω) (K.isOpen.mem_nhds K.zero),
      (K.horiz m' x _ (hb.corr_iff.2 rfl) ω).symm⟩

end Main

theorem jetZeta : GlobalTheory.Published.AbelianDeRham → JetCalc → JetZeta := by
  intro H hC
  refine ⟨1, ?_⟩
  intro ε E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G K i
  rw [_root_.one_mul]
  obtain ⟨a, a1, a2⟩ := exists_comb _ T.U.u.full (Pi.single (T.U.e.symm i) 1)
  obtain ⟨b, b1, b2⟩ := exists_comb_anti _ T.U.u.full (Pi.single (T.U.e.symm i) 1)
  obtain ⟨d, d1, d2, hd⟩ := low_anti H hφ hc T K.per i b1 b2
  have hV := K.isOpen.mem_nhds K.zero
  have m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) ((Category.comp_id _).trans (Category.id_comp _).symm) G.pull.grp
  have hb := isBC H T.X Y.mor
  obtain ⟨ω, hω, h0⟩ := exists_period_ne_zero H K K.zero (c := a) (a := T.U.e.symm i) (by simp [a1, a2])
  have hζ : AnalyticAt ℂ (fun z ↦ K.ζ z i) 0 := SCV.analyticAt_of_differentiableOn (differentiableOn_pi.1 K.ζ_hol i) hV
  have ja := hasJet_period hC K hb m' a ω
  have jb := hasJet_period hC K hb m' b ω
  have jd := hasJet_period hC K hb m' d ω
  have eb : period K b ω =ᶠ[𝓝 0] fun z ↦ K.ζ z i * period K a ω z := Filter.eventually_of_mem hV fun z hz ↦
    period_eq H K hz (fun m ↦ by
      by_cases hm : m = T.U.e.symm i
      · simp [a1, a2, b1, b2, hm]
      · simp [a1, a2, b1, b2, hm]) hω
  have ed : period K d ω =ᶠ[𝓝 0] fun z ↦ -(((ε : ℤ) : ℂ) * T.A i) * period K a ω z := Filter.eventually_of_mem hV fun z hz ↦
    period_eq H K hz (fun m ↦ by
      by_cases hm : m = T.U.e.symm i
      · simp [a1, a2, d1, d2, hm]
      · simp [a1, a2, d1, d2, hm]) hω
  have fb := jb.2.symm.trans ((Check.jet_congr J eb).trans (HasJet.mul hC ⟨hζ, rfl⟩ ⟨ja.1, rfl⟩).2)
  have fd := jd.2.symm.trans ((Check.jet_congr J ed).trans (HasJet.mul hC (hasJet_const _) ⟨ja.1, rfl⟩).2)
  have hF : Finsupp.linearCombination ℂ K.P₀ b ∈ Fil T.X.A :=
    (mem_Fil_iff T.U.u (H.2.1 ℂ T.X.A _ T.X.ab T.X.dim).1 (exists_lie_comb T.U.u K.P₀ _ K.per.2.2.1 b)).2 b1
  have hJ : IsJetElt J T.X T.low Y.mor (Finsupp.linearCombination ℂ K.P₀ b)
      (hb.bcMap (Finsupp.linearCombination ℂ K.P₀ b) + J.t i • hb.bcMap (Finsupp.linearCombination ℂ K.P₀ d)) := fun cc ↦ by
    rw [LinearMap.add_apply, LinearMap.smul_apply, hb.corr_iff.2 rfl cc, hb.corr_iff.2 rfl cc, Finset.sum_eq_single i, hd,
      if_pos rfl, smul_eq_mul]
    · intro k _ hk
      rw [hd, if_neg hk, LinearMap.zero_apply, map_zero, mul_zero]
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  have hz := (Submodule.mem_dualAnnihilator _).1 (Y.fil _ hF _ hJ) (m'.pull ω) (m'.isMor.pullback1_mem_hodgeFiltration hω)
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, fb, fd, smul_eq_mul, map_neg] at hz
  refine (isUnit_jet hC J ja.1 h0).mul_right_cancel ?_
  rw [Algebra.smul_def]
  linear_combination hz

end GlobalTheory.LatJet.An.ZetaNonvanishing₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquivStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  first | exact @GlobalTheory.FieldPair.adjKlt_ringEquiv | exact GlobalTheory.FieldPair.adjKlt_ringEquiv | (intros; apply GlobalTheory.FieldPair.adjKlt_ringEquiv <;> assumption)
end

