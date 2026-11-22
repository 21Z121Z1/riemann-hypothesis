import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3181
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplica
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMComm

theorem commute_of_cyclic {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.IsTorsionFree ℤ_[l] T] {O : Type} [CommRing O] (ρ : O →+* Module.End ℤ_[l] T) (v : T) (c : ℤ_[l])
    (hc : c ≠ 0) (hv : ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v))
    (g h : Module.End ℤ_[l] T) (hg : ∀ a, g * ρ a = ρ a * g) (hh : ∀ a, h * ρ a = ρ a * h) :
    g * h = h * g := by
  set P := Submodule.span ℤ_[l] (Set.range ρ) with hP
  have hcen : ∀ k : Module.End ℤ_[l] T, (∀ a, k * ρ a = ρ a * k) → ∀ x ∈ P, k * x = x * k := by
    intro k hk x hx
    have : P ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℤ_[l] {k}) := by
      rw [hP, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hk a
    have h1 := this hx
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at h1
    exact h1 k rfl
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hx' : ∀ a, x * ρ a = ρ a * x := fun a => by
      have := hcen (ρ a) (fun b => by rw [← map_mul, ← map_mul, mul_comm]) x hx
      exact this.symm
    exact hcen x hx' y hy
  have hev : ∀ w : T, ∃ x ∈ P, x v = c • w := by
    intro w
    have := hv w
    rw [show (Set.range fun a => ρ a v) = (LinearMap.applyₗ v : Module.End ℤ_[l] T →ₗ[ℤ_[l]] T) '' Set.range ρ by
      rw [← Set.range_comp]; rfl, Submodule.span_image] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  refine LinearMap.ext fun t => ?_
  obtain ⟨x, hx, ex⟩ := hev t
  obtain ⟨y, hy, ey⟩ := hev (g v)
  obtain ⟨z, hz, ez⟩ := hev (h v)
  have hgx := hcen g hg x hx
  have hhx := hcen h hh x hx
  have k1 : c • c • c • (g * h) t = x (z (y v)) := by
    have e1 : c • (g * h) t = x (g (h v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (g * (h * x)) v = x (g (h v))
      rw [hhx, ← _root_.mul_assoc, hgx, _root_.mul_assoc]; rfl
    have e2 : c • x (g (h v)) = x (z (g v)) := by
      rw [← map_smul, ← map_smul, ← ez]
      change x ((g * z) v) = x ((z * g) v)
      rw [hcen g hg z hz]
    rw [e1, e2, ← map_smul, ← map_smul, ← ey]
  have k2 : c • c • c • (h * g) t = x (y (z v)) := by
    have e1 : c • (h * g) t = x (h (g v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (h * (g * x)) v = x (h (g v))
      rw [hgx, ← _root_.mul_assoc, hhx, _root_.mul_assoc]; rfl
    have e2 : c • x (h (g v)) = x (y (h v)) := by
      rw [← map_smul, ← map_smul, ← ey]
      change x ((h * y) v) = x ((y * h) v)
      rw [hcen h hh y hy]
    rw [e1, e2, ← map_smul, ← map_smul, ← ez]
  have k3 : x (z (y v)) = x (y (z v)) := by
    change (x * (z * y)) v = (x * (y * z)) v
    rw [hcomm z hz y hy]
  have k4 : (c * c * c) • (g * h) t = (c * c * c) • (h * g) t := by
    rw [mul_smul, mul_smul, k1, k3, ← k2, mul_smul, mul_smul]
  exact smul_right_injective T (mul_ne_zero (mul_ne_zero hc hc) hc) k4

theorem galTate_comm_actTate {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] {O : Type} [CommRing O] (α : OAct O A) (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (a : O) :
    galTate A l σ * actTate α.toRingAct l (ptOver K Ω) a = actTate α.toRingAct l (ptOver K Ω) a * galTate A l σ :=
  LinearMap.ext fun t => Tate.ext fun n => by
    change specAut σ ≫ (t.lev n ≫ α.act a) = (specAut σ ≫ t.lev n) ≫ α.act a
    rw [Category.assoc]

theorem galTate_commute_of_hasCMBy : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  intro K Ω _ _ _ _ A _ _ hA F _ _ hF l _ hl σ τ
  obtain ⟨⟨d, hd, hdeg⟩, O, _, _, _, ⟨α⟩⟩ := hF
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hcard : ∀ n : ℕ, Nat.card {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} = l ^ (2 * d * n) := fun n => by
    rw [GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hd (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm n]
  obtain ⟨hfree, hfin, hrank⟩ := GlobalTheory.TateFree.free_finite_finrank (ptOver K Ω ⟶ A) l (2 * d) hcard
  haveI := hfree
  haveI := hfin
  obtain ⟨v, c, hc, hv⟩ := GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice l (Tate l (ptOver K Ω ⟶ A)) O F (actTate α.toRingAct l (ptOver K Ω))
    (hrank.trans hdeg.symm) (GlobalTheory.T.linearIndependent_numberFieldEndomorphisms_tateModule K Ω A hA
      ⟨d, by have := Module.finrank_pos (R := ℚ) (M := F); omega, hd⟩ F O α l hl)
  exact commute_of_cyclic _ v c hc hv _ _ (galTate_comm_actTate A α l σ) (galTate_comm_actTate A α l τ)

end GlobalTheory.CMComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  first | exact @GlobalTheory.Mum.TensAct.qkAct_tens | exact GlobalTheory.Mum.TensAct.qkAct_tens | (intros; apply GlobalTheory.Mum.TensAct.qkAct_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantLeCommonBoundMonomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_le_commonBound_monomial : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : Fin 8 → X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (mono W t δ w))) := by
  first | exact @GlobalTheory.Poinc.Sep.DivBound.theta_pow_le | exact GlobalTheory.Poinc.Sep.DivBound.theta_pow_le | (intros; apply GlobalTheory.Poinc.Sep.DivBound.theta_pow_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitivePrincipallyPolarisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem exists_embed_integral {V W K : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Field K]
    [IsAlgClosed K] (g : V →+* W) (hg : g.IsIntegral) (hgi : Function.Injective g) (j : V →+* K)
    (hj : Function.Injective j) : ∃ j' : W →+* K, j'.comp g = j ∧ Function.Injective j' := by
  letI := g.toAlgebra
  letI := j.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨hg⟩
  haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hgi
  haveI : Module.IsTorsionFree V K := Module.isTorsionFree_iff_algebraMap_injective.2 hj
  let f : W →ₐ[V] K := IsAlgClosed.lift
  have hc : f.toRingHom.comp (algebraMap V W) = j := RingHom.ext fun a => f.commutes a
  refine ⟨f.toRingHom, hc, ?_⟩
  have hk : (RingHom.ker f.toRingHom).comap (algebraMap V W) = ⊥ := by
    rw [RingHom.comap_ker, hc]
    exact (RingHom.injective_iff_ker_eq_bot j).1 hj
  exact (RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot hk)

theorem prim_descend {V W K K' : Type} [CommRing V] [CommRing W] [Field K] [Field K'] (g : V →+* W)
    (hg : g.IsIntegral) (i : V →+* K) (k : K →+* K') (i' : W →+* K') (h : i'.comp g = k.comp i) {J : Type}
    (c : J → K) (hp : Prim i' (fun a => k (c a))) : Prim i c := by
  have up : ∀ x : K', i'.IsIntegralElem x → (k.comp i).IsIntegralElem x := by
    intro x hx
    letI := g.toAlgebra
    letI := i'.toAlgebra
    letI := (k.comp i).toAlgebra
    haveI : Algebra.IsIntegral V W := ⟨hg⟩
    haveI : IsScalarTower V W K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun h a).symm
    exact isIntegral_trans (R := V) (A := W) x hx
  have down : ∀ y : K, (k.comp i).IsIntegralElem (k y) → i.IsIntegralElem y := by
    rintro y ⟨p, hm, he⟩
    refine ⟨p, hm, k.injective ?_⟩
    rw [map_zero, Polynomial.hom_eval₂]
    exact he
  refine ⟨fun a => down _ (up _ (hp.1 a)), ?_⟩
  obtain ⟨a, ha, hinv⟩ := hp.2
  refine ⟨a, fun e => ha (by simp [e]), down _ ?_⟩
  rw [map_inv₀]
  exact up _ hinv

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (g : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hc, hL⟩ := h
  have g₁ := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left,
      ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ :=
    hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ) :=
    (GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm
  have hq := amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L
    (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩

theorem thList_move {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {T : Over S} (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    (h₁ : Over.mk x₁ ⟶ T) (h₂ : Over.mk x₂ ⟶ T) (hl : h₁.left = h₂.left) {N : ℕ} (pt : Fin N → (Over.mk x₁ ⟶ G))
    (c : Fin N → K) (hT : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ s) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ s) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext hl
  exact ⟨pt, hT⟩

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem prim_of_polFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S), PolFib t.G t.PP.L g (jK V ≫ χ) → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t g V _ _ _ hV χ hpf σ hσ m N hm hm3 hmu K _ i pt c hi hT
  obtain ⟨hd, hc, h0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  haveI := hd
  haveI := h0
  obtain ⟨t₁, ⟨m₁⟩⟩ : ∃ t₁ : SAB H (Sp V), Nonempty (SABMap t₁ t χ) := by
    obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, m', -⟩ := sabPull Out.CubePf.cubePull χ t
    exact ⟨_, ⟨m'⟩⟩
  obtain ⟨W, _, _, _, _, gW, hcW, hgi, hginj, hgl, Ex, hEx⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hc t₁.G t₁.semi
  obtain ⟨t₂, m₂, hS⟩ : ∃ (t₂ : SAB H (Sp W)) (_ : SABMap t₂ t₁ (spMap gW)),
      ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t₂.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m', -⟩ := sabPull Out.CubePf.cubePull (spMap gW) t₁
    exact ⟨_, m', Ex, hEx⟩
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
  have hp0 : GlobalTheory.LN.PolAt t (jK V ≫ χ) := polAt_of_polFib t g _ hpf
  have hp1 := GlobalTheory.DatUniq.polAt_pull m₁ hp0 (jK V) (𝟙 _) (Category.id_comp _)
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp gW) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  let gam : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg' : ∀ r, gam (algebraMap _ _ r) = algebraMap W _ (gW r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value gam
  have hgam : spMap gam ≫ jK V = jK W ≫ spMap gW := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg'))
  have hp2 := GlobalTheory.DatUniq.polAt_pull m₂ hp1 (jK W) (spMap gam) hgam
  have hW : GlobalTheory.LN.CDvr W := (GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hcW, inferInstance⟩
  obtain ⟨U, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t₂ hp2 hS
  have hσ' := nz_pull S t.G t.PP.L t.PP.isLB t.semi V W χ σ gW hσ
  have hmuW : IsUnit (m : W) := by simpa using hmu.map gW
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨i', hi'c, hi'⟩ := exists_embed_integral gW hgi hginj (k.comp i) (k.injective.comp hi)
  obtain ⟨pt₁, -, hT₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K (AlgebraicClosure K) k
    (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c hT
  let a₁ : Over.mk (spMap k ≫ spMap i ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (spMap k) rfl
  let a₂ : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let b₁ : Over.mk (spMap i' ≫ spMap gW ≫ χ) ⟶ Over.mk (spMap gW ≫ χ) := Over.homMk (spMap i') rfl
  let b₂ : Over.mk (spMap gW ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap gW) rfl
  have e₁ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) k = VVRank.pullS t.G _ (a₁ ≫ a₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have e₂ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ gW) i' = VVRank.pullS t.G _ (b₁ ≫ b₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have hx : spMap i' ≫ spMap gW = spMap k ≫ spMap i := by
    rw [spMap_comp_eq', spMap_comp_eq', hi'c]
  rw [e₁] at hT₁
  obtain ⟨pt₂, hT₂⟩ := thList_move t.G t.PP.L t.PP.rig m σ (by rw [← Category.assoc, ← hx, Category.assoc])
    (a₁ ≫ a₂) (b₁ ≫ b₂) (by simp [a₁, a₂, b₁, b₂, hx]) pt₁ _ hT₁
  rw [← e₂] at hT₂
  exact prim_descend gW hgi i k i' hi'c c
    (GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H S t W hW (spMap gW ≫ χ) t₂ ⟨n⟩ ⟨U⟩ _ hσ' m N hm hm3 hmuW _ i' pt₂ _ hi' hT₂)

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionRationalPointsInvariantTriple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RatInvTheta

theorem inclR_inj (D : D7) : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem sigR_inclR (D : D7) (e : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (F := D.host.F) (AF D.host.F) e) =
      inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig e) := by
  simp [sigR, inclR]

theorem mem_GQ_of {D : D7} (V : HSp D) (g : GA D V) (z : GL (Fin V.rank) D.host.E)
    (hz : mt V g = (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) :
    g ∈ GQ V := by
  refine ⟨z, ?_, Units.ext ?_⟩
  · have hm : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
        JR (AF D.host.F) V.gram := g.2
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
        ((z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map
          (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact sigR_inclR D _
    rw [hz, hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram
    apply Matrix.map_injective (inclR_inj D)
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hz.symm

theorem thetaSum_rat_inv : ∀ {D : D7} {a a' : ℕ} (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ γ ∈ ratU D.sp.cm.sig Γ.V.J, ∀ γ' ∈ ratU D.sp.cm.sig Γ.W.J, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin a × Fin (a + a')),
      GlobalTheory.WeilM.thetaSum D.host.F (om (γ, γ') Φ) = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  intro D a a' Bs Γ X om om' hT γ hγ γ' hγ' Φ hΦ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hT.base a Γ.V _ _ hT.geo.hV
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hT.base (a + a') Γ.W _ _ hT.geo.hW
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hT.geo.hV.lat h3 (fun _ => (a - Γ.p, Γ.p))
  let S := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 L hL h6
    (fun _ => (Γ.p + Γ.q, a + a' - (Γ.p + Γ.q)))
  have eA : Γ.V.J = T.gramᵀ := by rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E (X.β / X.α) :=
    ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]⟩
  have rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range (X.β / X.α)
      (a + a') := by
    intro x
    have e₁ := hT.chars.resβ x
    have e₂ := hT.chars.resα x
    rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hT.geo.even.neg_one_pow]
    split_ifs
    · simp
    · rcases Nat.even_or_odd a with h | h
      · have h' : Even a' := (Nat.even_add.mp hT.geo.even).mp h
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
      · have h' : Odd a' := by
          rcases Nat.even_or_odd a' with h'' | h''
          · exact absurd ((Nat.even_add.mp hT.geo.even).mpr h'') (Nat.not_even_iff_odd.mpr h)
          · exact h''
        rw [h.neg_one_pow, h'.neg_one_pow]; simp
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hT.base S T Γ.V Γ.W _ _ _ _ hT.geo.hV hT.geo.hW
    eA eB Γ.M hT.geo.hM X.β (X.β / X.α) hT.chars.heckeβ hcW hT.chars.resβ rW om hT.weil
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.WeilSchrodinger.match_pair D S T Γ.V.J Γ.W.J (-1) eA eB γ γ'
  obtain ⟨z, hz⟩ := hγ
  obtain ⟨z', hz'⟩ := hγ'
  have hhQ : h ∈ GQ T := by
    refine mem_GQ_of T h z ?_
    rw [hh]
    exact (congrArg Units.val hz).symm
  have hgQ : g ∈ GQ S := by
    have m1 := congrArg Matrix.transpose (Units.mul_inv z')
    have m2 := congrArg Matrix.transpose (Units.inv_mul z')
    rw [Matrix.transpose_mul, Matrix.transpose_one] at m1 m2
    let Z : GL (Fin (a + a')) D.host.E :=
      ⟨((z'⁻¹ : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ,
        ((z' : GL (Fin (a + a')) D.host.E) : Matrix (Fin (a + a')) (Fin (a + a')) D.host.E)ᵀ, m1, m2⟩
    refine mem_GQ_of S g Z ?_
    rw [hg]
    have h0 : γ'.1 = Matrix.GeneralLinearGroup.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) z' := hz'.symm
    show ((γ'.1)⁻¹ : GL (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)).1ᵀ = _
    rw [h0, ← map_inv]
    rfl
  have hf :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D Bs.ψ (GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D Bs.ψ hT.base.std) S T Γ.V.J Γ.W.J (-1) eA eB (Fin T.rank × Fin S.rank) Γ.M.co
      hT.geo.hM.rat Φ hΦ
  have key := hth γ γ' g h hh hg Φ hΦ
  have e0 := GlobalTheory.WeilBridge.thetaTr_zero D Γ.M.co Bs.ψ Φ
  have e1 := hω.om_aut g hgQ h hhQ _ hf
  exact key.trans (e1.trans e0)

end GlobalTheory.RatInvTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlace
section
noncomputable section

namespace GlobalTheory.KeyBadPrime

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem key_unit_bad : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c κ hκ hpq la p hp hpl hbad T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk
  obtain ⟨l₂, hd, hA, hg₂⟩ := GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart E H l
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₂ hpq
  obtain ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, x₂, r, m, he', hv, hφ, ho₂, hxs₂, hx₂⟩ :=
    GlobalTheory.T.modulipoint_lift_to_finerLevel_completeDVR E H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hxs
  obtain ⟨G', t'', mt, m2', n', w', θ', k', hw', hθ', hk', hpb⟩ := GlobalTheory.T.exists_integralFramedData_completeDVR_extension E H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨m1', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m (PullbackSections.sabMapCast a₁ hx₂.symm)
  obtain ⟨u', hu'⟩ := GlobalTheory.KeyIntegralVal.key_unit hκ hpq hg₂ ho₂ hxs₂ m1' m2' hw' hθ' k' hk'
  have h1 : (κ T'.Fr k' : T'.Fr) = iT (κ T.Fr k : T.Fr) := hκ.2.1 T.Fr T'.Fr iT k k' hpb
  set a : T.Fr := (κ T.Fr k : T.Fr) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hu0 : ∀ (V : CDVR) (u : V.Vˣ), vV V.V (algebraMap V.V V.Fr u) = 0 := by
    intro V u
    have hne : ∀ u : V.Vˣ, algebraMap V.V V.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
    have nn : ∀ b : V.V, 0 ≤ vV V.V (algebraMap V.V V.Fr b) := fun b => by
      by_cases h : algebraMap V.V V.Fr b = 0
      · simp [h, vV]
      have := (WithZero.log_le_log (valV_ne_zero (V := V.V) h) one_ne_zero).2
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b)
      rw [WithZero.log_one] at this
      rw [vV]; omega
    have h := vV_mul (V := V.V) (hne u) (hne u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV V.V (1 : V.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : V.Vˣ)
    omega
  have hva : vV T.V a = 0 := by
    have h2 := hv a
    rw [← h1, hu', hu0] at h2
    have : (0 : ℤ) < e' := by exact_mod_cast he'
    nlinarith
  have hvi : vV T.V a⁻¹ = 0 := by
    have h := vV_mul (V := T.V) ha0 (inv_ne_zero ha0)
    rw [mul_inv_cancel₀ ha0, show vV T.V (1 : T.Fr) = 0 by simp [vV], hva] at h
    omega
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hva.ge
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hvi.ge
  have hbb : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', mul_inv_cancel₀ ha0, map_one])
  exact ⟨⟨b, b', hbb, by rw [mul_comm]; exact hbb⟩, hb.symm⟩

end GlobalTheory.KeyBadPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemmaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  first | exact @GlobalTheory.Mum.thetaLevels_galois | exact GlobalTheory.Mum.thetaLevels_galois | (intros; apply GlobalTheory.Mum.thetaLevels_galois <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  first | exact @GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | exact GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | (intros; apply GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine <;> assumption)
end

