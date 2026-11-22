import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0006
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDegreeGeHalfDetLieDefinitePoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulId
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

variable (R A) in

def restrZeroLeft : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ (counit (R := R) (A := A)).rTensor A

theorem restrZeroLeft_tmul (a b : A) : restrZeroLeft R A (a ⊗ₜ b) = counit (R := R) a • b := by
  simp [restrZeroLeft]

theorem restrZeroLeft_comul (a : A) : restrZeroLeft R A (comul a) = a := by
  simp [restrZeroLeft, Coalgebra.rTensor_counit_comul]

variable (R A) in

def restrZeroZero : A ⊗[R] (A ⊗[R] A) →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ TensorProduct.map (counit (R := R) (A := A))
    (restrZeroLeft R A)

theorem restrZeroZero_tmul (a : A) (t : A ⊗[R] A) :
    restrZeroZero R A (a ⊗ₜ t) = counit (R := R) a • restrZeroLeft R A t := by
  simp [restrZeroZero]

theorem restrZeroZero_assoc (u : A ⊗[R] A) (b : A) :
    restrZeroZero R A (TensorProduct.assoc R A A A (u ⊗ₜ b)) =
      counit (R := R) (restrZeroLeft R A u) • b := by
  induction u with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy, add_smul]
  | tmul x y =>
    rw [TensorProduct.assoc_tmul, restrZeroZero_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul,
      map_smul, smul_eq_mul, mul_smul]

theorem restrZeroLeft_of_cobTwo_eq_zero {c : A ⊗[R] A} (hc : cobTwo R A c = 0) :
    restrZeroLeft R A c =
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) c)) := by
  have key : ∀ t : A ⊗[R] A, restrZeroZero R A (cobTwo R A t) = restrZeroLeft R A t -
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) t)) := fun t => by
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; abel
    | tmul a b =>
      rw [cobTwo_apply]
      simp only [map_sub, map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.flip_apply,
        TensorProduct.mk_apply, restrZeroZero_assoc, restrZeroZero_tmul, restrZeroLeft_comul,
        restrZeroLeft_tmul, Bialgebra.counit_one, one_smul, TensorProduct.map_tmul,
        TensorProduct.lid_tmul, smul_eq_mul, Algebra.algebraMap_eq_smul_one, mul_smul]
      abel
  have := key c
  rw [hc, map_zero] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem dUnit_mul'_map (f g : A →ₐc[R] B) (t : A ⊗[R] A) :
    dUnit R (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) t)) =
      cotMap g (dUnit R (restrZeroLeft R A t)) +
        cotMap f (dUnit R (restrZeroLeft R A (TensorProduct.comm R A A t))) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul a b =>
    have e1 : dUnit R (counit (R := R) a • b) = counit (R := R) a • dUnit R b :=
      map_smul (AugCot.d _) _ _
    have e2 : dUnit R (counit (R := R) b • a) = counit (R := R) b • dUnit R a :=
      map_smul (AugCot.d _) _ _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, restrZeroLeft_tmul,
      restrZeroLeft_tmul, e1, e2, map_smul, map_smul, cotMap_d, cotMap_d, dUnit, AugCot.d_mul]
    have c1 : counitAlgHom R B (f a) = counit (R := R) a := CoalgHomClass.counit_comp_apply f a
    have c2 : counitAlgHom R B (g b) = counit (R := R) b := CoalgHomClass.counit_comp_apply g b
    exact congrArg₂ (· + ·) (congrArg₂ (· • ·) c1 rfl) (congrArg₂ (· • ·) c2 rfl)

theorem dUnit_mul'_map_of_mem (f g : A →ₐc[R] B) {c : A ⊗[R] A} (hc : c ∈ symCocycles R A) :
    dUnit R (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) = 0 := by
  obtain ⟨h1, h2⟩ := mem_symCocycles.1 hc
  rw [dUnit_mul'_map, h2, restrZeroLeft_of_cobTwo_eq_zero h1, dUnit, AugCot.d_algebraMap,
    map_zero, map_zero, zero_add]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R}

theorem rigExtMap_add (f g : G ⟶ H) : rigExtMap (f + g) = rigExtMap f + rigExtMap g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  let B : G.funs := ⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n)
      (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by
    dsimp only
    rw [← (c.2 n).2]
    generalize c.1 (n + 1) = t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [res_app]⟩
  have hB : G.dFun B = 0 :=
    Subtype.ext (funext fun n => dUnit_mul'_map_of_mem (f.app n) (g.app n) (c.2 n).1)
  have hc : cocyclesMap (f + g) c = cocyclesMap f c + cocyclesMap g c + G.cob B :=
    Subtype.ext (funext fun n => T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1)
  change G.rigMk (cocyclesMap (f + g) c, omegaMap G H (f + g) w) =
    G.rigMk (cocyclesMap f c, omegaMap G H f w) + G.rigMk (cocyclesMap g c, omegaMap G H g w)
  rw [← map_add, Prod.mk_add_mk, map_add (omegaMap G H) f g, LinearMap.add_apply, hc]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · show G.cob B = _
    simp
  · show G.dFun B = _
    rw [hB]
    simp

variable (G) in

theorem rigExtMap_natCast_smul_id (hp : (p : R) = 0) : rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  let φ : (G ⟶ G) →+ (G.RigExt →ₗ[R] G.RigExt) :=
    AddMonoidHom.mk' (fun f => rigExtMap f) (fun f g => rigExtMap_add f g)
  have h : φ (p • 𝟙 G) = p • φ (𝟙 G) := map_nsmul φ p (𝟙 G)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul] at h
  exact h

theorem rigExtMap_add_and_natCast_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G H : PDivGroup p R),
    (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧
      rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 :=
  fun _ _ _ _ h G _ => ⟨rigExtMap_add, G.rigExtMap_natCast_smul_id h⟩

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalar
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

open GlobalTheory.VolBr.NuEq in

theorem val_frame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  intro k _ X _ p P a b σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have hL : CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG
  have hA : CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG'
  set gL := CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y with hgL
  set gA := CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y with hgA
  have hG : gL ^ a * gA ^ b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hL) (zpow_ne_zero _ hA)
  have hGn : (‖gL ^ a * gA ^ b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hG)
  refine ⟨(‖gL ^ a * gA ^ b‖ : ℂ) / (gL ^ a * gA ^ b), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hG)]
  intro f hf
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have hrv : ratVal (P.loc a b f i j) y =
      gL ^ a * gA ^ b * ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y := by
    rw [hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
      ratVal_zpow' uG, ratVal_zpow' uG', eG, eG']
    rfl
  have c0 : 0 < ‖gL‖ := norm_pos_iff.2 hL
  have c0' : 0 < ‖gA‖ := norm_pos_iff.2 hA
  have hexp : Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) =
      ‖gL ^ a * gA ^ b‖⁻¹ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) := by
    rw [(P.L.φ σ).trans i _ y hi hi₀, (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_zpow, norm_zpow,
      ← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
      Real.log_pow, Real.log_pow, ← hgL, ← hgA, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [val, hrv, hexp]
  push_cast
  field_simp

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.FieldPt

theorem of_factor {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (V : M.Z.Opens) (v : V.toScheme ⟶ F.X) {T₀ : Scheme.{0}} (ξ : T₀ ⟶ V.toScheme)
    (cO : SiegPre g n ζ ((ξ ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (ξ ≫ V.ι)).obj FinalForm.G ⟶ cO.A))
    (hpbO : SiegPB cO F.univ (ξ ≫ v)) (hmonO : ∀ a, IsMonHom (prO a))
    (hunivO : ∀ (T' : Over T₀) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (ξ ≫ V.ι)).obj FinalForm.G,
      ∀ a, x ≫ prO a = y a)
    (hLO : LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι)))
      (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)))
    (hmatO : ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (ξ ≫ V.ι)).map f))
    {K : Type} [Field K] (t : Sp K ⟶ V.toScheme) (t' : Sp K ⟶ T₀) (ht : t' ≫ ξ = t)
    (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left) (hB : IsGrpPullback B FinalForm.G (t ≫ V.ι) φB) :
    ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧
      (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧
      (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧
      ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left →
        MatEnd pr' a b fB := by
  subst ht
  have hB' : IsGrpPullback B FinalForm.G (t' ≫ (ξ ≫ V.ι)) φB := hB.congr (Category.assoc _ _ _) rfl
  have hφ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (ξ ≫ V.ι) t' hB'
  have hφ'f : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) = φB :=
    pullback.lift_fst _ _ _
  have hφ's : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
      B.hom ≫ t' := pullback.lift_snd _ _ _
  generalize pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) = φ' at hφ hφ'f hφ's
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) _ (Sp K)
    ((ξ ≫ v) ≫ F.s) (((t' ≫ ξ) ≫ v) ≫ F.s) t' rfl (by rw [hid, Category.comp_id]; simp only [Category.assoc])).1 cO
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpbO hc'
  rw [← Category.assoc] at hcomp
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.GrpPullPow.pr_pull prO hφ hχ hmonO hunivO
  refine ⟨c', pr', hcomp, hmon', huniv', ?_, ?_⟩
  · intro L' hL' hiso
    have hL := FinalForm.L.isLB
    have e1 : LBIso (FinalForm.L.L.pull φB) ((FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))).pull φ') := by
      rw [← hφ'f]
      exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame FinalForm.L.L _ _ _ φ' fun _ => rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))) φ' φ' rfl)
        ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso _, ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen (pull_isLB hL _)⟩
    have e2 := LBIso.trans hL' (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hiso e1
    exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull cO.P c'.P _ L' prO pr' W cO.isLB c'.isLB (pull_isLB hL _) hL' hsq hP hpr'
      e2 hLO
  · intro a b f fB hf hfB
    refine GlobalTheory.MatEndPull.matEnd_pull prO pr' a b _ fB hφ hχ hpr' ?_ (hmatO a b f hf)
    apply pullback.hom_ext
    · have e : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.fst FinalForm.G.hom (ξ ≫ V.ι) ≫ f.left := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, hφ'f, e, ← Category.assoc, hφ'f, hfB]
    · have w1 : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.snd FinalForm.G.hom (ξ ≫ V.ι) := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, hφ's, w1, hφ's, ← Category.assoc, Over.w fB]

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv K _ t B _ φB hB
  obtain ⟨cO, prO, hpbO, hmonO, hunivO, hLO, hmatO⟩ := GlobalTheory.T.eighth_power_universal_object_at_model_stalk g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
    (t (IsLocalRing.closedPoint K))
  exact of_factor F W FinalForm pr V v _ cO prO hpbO hmonO hunivO hLO hmatO t _
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t) B φB hB

end GlobalTheory.Poinc.Eq8.FieldPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.TorusExt

theorem periods_of_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ E E' : EndU U₁.toUnifPre, LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L) (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E'.aG] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ c, snd A₁.A A₁.A ≫ c] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], Key U₁.toUnifPre U₂.toUnifPre c b h F → ∃ φ : D₁.toPre.X →+ D₂.toPre.X, (∀ (y : D₁.toPre.X) (g : GtPtF D₁.toPre F), GtPtF.IsIota y g → ∃ g' : GtPtF D₂.toPre F, Act D₁.toPre D₂.toPre b h g g' ∧ GtPtF.IsIota (φ y) g') ∧ ∀ y, h (φ y) = E.h y := by
  intro R _ _ _ I hA D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hco E E' hE hW F _ _ _ hkey
  have hL := GlobalTheory.firstFiveLaws
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  letI := gtGroup D₁.toPre F
  letI := gtGroup D₂.toPre F
  have hB₁ := D₁.tau_bimult
  have hB₂ := D₂.tau_bimult
  have inj₂ := GlobalTheory.IotaInj.main hL R I hA D₂ F
  have dv₁ := (gt_onto_divisible_kernel hL R I hA D₁ F).2.1

  obtain ⟨ex, ad, tor⟩ := GlobalTheory.T.torusExtensionMap_welldefined_additive_characters R D₁.toPre D₂.toPre b h hlin.2.1 (fun χ => (hco χ).imp fun _ hu => hu.1) F
  choose mf hmf hmu using ex
  let m : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' mf fun x x' => (isAdd_iff_eq _ _ _).1
    (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hmf x) (hmf x') (hmf _))
  have hm : ∀ x x', Act D₁.toPre D₂.toPre b h x x' ↔ x' = m x := fun x x' => ⟨hmu x x', fun e => e ▸ hmf x⟩

  have push : ∀ k : ℕ, 1 ≤ k → ∀ f₁ f₂, Tors U₁.toUnifPre F k f₁ → Tors U₂.toUnifPre F k f₂ → ∀ p : QkPt D₁.toPre F k,
      ∃ p' : QkPt D₂.toPre F k, p'.g = m p.g ∧ f₂ p' = f₁ p ≫ c ∧ GtPtF.IsIota p'.y (m (iota hB₁ F p.y)) := by
    intro k hk f₁ f₂ hf₁ hf₂ p
    obtain ⟨p', e₁, e₂⟩ := hkey k hk p (f₁ p) ((hf₁.1 _ _).2 rfl) (m p.g) ((hm _ _).2 rfl)
    refine ⟨p', e₁, ((hf₂.1 _ _).1 e₂).symm, (isIota_iff_eq hB₂ _ _).2 ?_⟩
    rw [← qk_nsmul hB₂ p', e₁, ← map_nsmul, qk_nsmul hB₁ p]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F 1 le_rfl
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F 1 le_rfl
  have ex₁ : ∀ y, ∃ y', GtPtF.IsIota y' (m (iota hB₁ F y)) := fun y => by
    obtain ⟨p', -, -, hp'⟩ := push 1 le_rfl f₁ f₂ hf₁ hf₂ (qkMk hB₁ y (iota hB₁ F y) (one_smul _ _))
    exact ⟨p'.y, hp'⟩
  choose φ₀ hφ₀ using ex₁
  let φ : D₁.toPre.X →+ D₂.toPre.X := AddMonoidHom.mk' φ₀ fun y y' => inj₂ _ _ _ (hφ₀ (y + y'))
    ((isIota_iff_eq hB₂ _ _).2 (by
      rw [map_add, map_add, map_add, ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y), ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y')]))
  have hφ : ∀ y, GtPtF.IsIota (φ y) (m (iota hB₁ F y)) := hφ₀
  refine ⟨φ, fun y g hg => ⟨m g, (hm _ _).2 rfl, ?_⟩, fun y => ?_⟩
  · rw [(isIota_iff_eq hB₁ _ _).1 hg]; exact hφ y
  refine GlobalTheory.KeyIota.eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F k hk
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F k hk
  have wp₁ := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL R I hA D₁ F k hk
  have wp₂ := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL R I hA D₂ F k hk
  have torp : ∀ p : QkPt D₁.toPre F k, f₁ p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U₁.toUnifPre.ext
    exact ((hf₁.1 p _).2 rfl w hw).1

  obtain ⟨gk, hgk⟩ := dv₁ k hk (iota hB₁ F y)
  let p : QkPt D₁.toPre F k := ⟨y, gk, _, hgk, (isIota_iff_eq hB₁ _ _).2 rfl⟩
  obtain ⟨p', -, hpp', hp'⟩ := push k hk f₁ f₂ hf₁ hf₂ p
  have hyp' : p'.y = φ y := inj₂ _ _ _ hp' (hφ y)

  have h0 : k • torusPt D₁.toPre F (Additive.ofMul t) = iota hB₁ F 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero, map_zero]
  let q : QkPt D₁.toPre F k := qkMk hB₁ 0 (torusPt D₁.toPre F (Additive.ofMul t)) h0
  have hq : IsTor t q.g := (isTor_iff _ _).2 (isTorusPtF_torusPt t)
  obtain ⟨q', hqg, hqq', hq'i⟩ := push k hk f₁ f₂ hf₁ hf₂ q
  have hq'0 : q'.y = 0 := inj₂ _ _ _ hq'i ((isIota_iff_eq hB₂ _ _).2 (by
    show m (iota hB₁ F 0) = iota hB₂ F 0
    simp only [map_zero]))
  have hq'tor : IsTor (t.comp (AddMonoidHom.toMultiplicative h)) q'.g := tor t q.g q'.g hq ((hm _ _).2 hqg)

  have ec := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hA D₁ A₁ G₁ hG₁ U₁ F E E E
  have adE := ec.2.1
  choose aEf haE huE using ec.1
  let aE : GtPtF D₁.toPre F →+ GtPtF D₁.toPre F := AddMonoidHom.mk' aEf fun x x' => (isAdd_iff_eq _ _ _).1
    (adE x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (haE x) (haE x') (haE _))
  have hqE0 : k • aE q.g = iota hB₁ F 0 := by
    rw [← map_nsmul]
    show aE (k • torusPt D₁.toPre F (Additive.ofMul t)) = _
    simp only [h0, map_zero]
  let qE : QkPt D₁.toPre F k := qkMk hB₁ 0 (aE q.g) hqE0
  have hqEtor : IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) qE.g := ec.2.2.1 t q.g qE.g hq (haE q.g)
  have hFu := (GlobalTheory.UT.functorial_of_unif R I hA D₁ A₁ G₁ hG₁ U₁).2 E E' hE
  have hqE : f₁ qE = f₁ q ≫ E.aA := ((hf₁.1 _ _).1 ((hFu.2 F).2.2 k hk q qE (f₁ q)
    (by show (0 : D₁.toPre.X) = E'.h 0; rw [map_zero]) (haE q.g) ((hf₁.1 _ _).2 rfl))).symm

  have w₁ := (hf₁.2.2.2.2 _ _ _).1 ((wp₁ qE p).2 (t.comp (AddMonoidHom.toMultiplicative E.h)) rfl hqEtor)
  rw [hqE, ← Category.comp_id (f₁ p)] at w₁
  have w₂ := (GlobalTheory.T.commutator_pairing_eq_of_mumford_bundle_iso _ A₁ A₂ A₁ c c E.aA (𝟙 _) hc hc E.homA inferInstance hW F _ k (f₁ q) (f₁ p)
    (torp q) (torp p) _).2 w₁
  rw [← hqq', ← hpp'] at w₂
  have w₃ := (hf₂.2.2.2.2 _ _ _).2 w₂
  have e := (wp₂ q' p').1.unique w₃ ((wp₂ q' p').2 _ hq'0 hq'tor)
  rw [hyp'] at e
  exact e.symm

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmoothStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_pull_of_genericallySmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E := by
  first | exact @GlobalTheory.HermLB.semiPos_pull_of_genSmooth | exact GlobalTheory.HermLB.semiPos_pull_of_genSmooth | (intros; apply GlobalTheory.HermLB.semiPos_pull_of_genSmooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRaiseWeightSegmentSmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem semiPos_up_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p)
    (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  intro k _ X p D L u t h0 h1 hL hLu σ i c y hy ξ
  set f : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => (L.φ σ).φ i (c.e.symm v) with hfdef
  set g : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => u.u σ (c.e.symm v) with hgdef
  have hf : ContDiffAt ℝ 2 f (c.e y) := (L.cInf σ).contDiffAt c hy.1 hy.2
  have hfg : ContDiffAt ℝ 2 (fun v => f v + g v) (c.e y) := ((up L u).cInf σ).contDiffAt c hy.1 hy.2
  have a : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (f v : ℂ)) (c.e y) ξ).re := hL σ i c y hy ξ
  have b : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((f v + g v : ℝ) : ℂ)) (c.e y) ξ).re := hLu σ i c y hy ξ
  have e : (fun v => (((up L (u.smul t)).φ σ).φ i (c.e.symm v) : ℂ)) =
      fun v => ((((1 - t) * f v + 0) + (t * (f v + g v) + 0) : ℝ) : ℂ) := by
    funext v
    show ((((L.φ σ).φ i (c.e.symm v) + t * u.u σ (c.e.symm v)) : ℝ) : ℂ) = _
    congr 1
    simp only [hfdef, hgdef]
    ring
  rw [e, ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add, ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hf,
    ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (f := fun v => f v + g v) hfg]
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (hf.const_smul (1 - t)).add contDiffAt_const
  · exact (hfg.const_smul t).add contDiffAt_const

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBaseStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_flagCellFibreDensity_eq_base : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  first | exact @GlobalTheory.FlagCell2.setLIntegral_fibDens | exact GlobalTheory.FlagCell2.setLIntegral_fibDens | (intros; apply GlobalTheory.FlagCell2.setLIntegral_fibDens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharpRef_of_refines_tensor : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_tens | exact GlobalTheory.Mum.PowData.sharpRef_of_tens | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDegreeGeHalfDetLieDefinitePointStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_degree_ge_half_detLie_definitePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z), (∑ τ : Psi H, P.degLie τ.1) / 2 + ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) ≤ P.degTh := by
  first | exact @GlobalTheory.DefPt.ThetaDeg.main | exact GlobalTheory.DefPt.ThetaDeg.main | (intros; apply GlobalTheory.DefPt.ThetaDeg.main <;> assumption)
end

