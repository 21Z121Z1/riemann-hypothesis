import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3357
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0333
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3358
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitOrdersEffectiveCartierExtendFromGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEquivOfSameCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LatCmp

theorem act_unit {Y : Type} [AddCommGroup Y] (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag {Y Y' : Type} [AddCommGroup Y] [AddCommGroup Y'] (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y'))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b)
    (v : Fin 8 → Y) (a : Fin 8) : θ v a = θ (Pi.single 0 (v a)) 0 := by
  have h1 := h (Matrix.of fun i' j' => if i' = a ∧ j' = a then (1 : ℤ) else 0) v
  rw [act_unit, act_unit] at h1
  have h2 := h (Matrix.of fun i' j' => if i' = a ∧ j' = 0 then (1 : ℤ) else 0) (Pi.single 0 (v a))
  rw [act_unit, act_unit] at h2
  have e1 := congrFun h1 a
  have e2 := congrFun h2 a
  simp only [Pi.single_eq_same] at e1 e2
  rw [← e1, e2]

theorem exists_diag {Y Y' : Type} [AddCommGroup Y] [AddCommGroup Y'] (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y'))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b) :
    ∃ κ : Y ≃ₗ[ℤ] Y', ∀ v : Fin 8 → Y, θ v = fun a => κ (v a) := by
  let κ0 : Y →+ Y' := (Pi.evalAddMonoidHom (fun _ : Fin 8 => Y') 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => Y) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ h v a
  have hsingle : ∀ y, θ (Pi.single 0 y) = Pi.single 0 (κ0 y) := by
    intro y; funext a; rw [hθ]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  have inj : Function.Injective κ0 := by
    intro y y' hy
    have : θ (Pi.single 0 y) = θ (Pi.single 0 y') := by rw [hsingle, hsingle, hy]
    exact Pi.single_injective 0 (θ.injective this)
  have surj : Function.Surjective κ0 := by
    intro y
    refine ⟨θ.symm (fun _ => y) 0, ?_⟩
    rw [← hθ]; simp
  refine ⟨(AddEquiv.ofBijective κ0 ⟨inj, surj⟩).toIntLinearEquiv, fun v => ?_⟩
  funext a
  exact hθ v a

end GlobalTheory.Poinc.LatCmp

theorem GlobalTheory.Poinc.lattice_equiv_of_same_centre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c c' : CTrait X₁ p z₁) (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (yy' : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c'.T.D.toPre.X)), IsLab X₁ ε₁ c yy → IsLab X₁ ε₁ c' yy' → ∃ κ : c.T.D.toPre.X ≃ₗ[ℤ] c'.T.D.toPre.X, ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (fun u => κ (μ u)) := by
  intro g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hε p _ z₁ c c' yy yy' h h'
  obtain ⟨Y, U₀, EE, FinalForm, q, hov, hee, hq, hpt, hcon, hlift⟩ := GlobalTheory.T.exists_semiabelianModel_proper_over_thetaSetup g n F W Z i X₁ hg hn ho hi he ht hp
  obtain ⟨y, hy⟩ := hlift p z₁ c
  obtain ⟨y', hy'⟩ := hlift p z₁ c'
  obtain ⟨θ, hl, hE⟩ := GlobalTheory.T.exists_labelled_lattice_equiv_of_common_fibre g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hε Y U₀ EE FinalForm q hov hee hq hpt p z₁ (hcon z₁) c c' y y' hy hy' yy yy' h h'
  obtain ⟨κ, hκ⟩ := GlobalTheory.Poinc.LatCmp.exists_diag θ hE
  refine ⟨κ, fun a μ hμ => ?_⟩
  rw [hl a μ hμ, hκ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestPositiveLevelsKappaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_test_positive_levels_kappa : Hypotheses3 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PLevW F ∧ (R.toCx3 F).PartsW false ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  first | exact @GlobalTheory.Stage3.stage3 | exact GlobalTheory.Stage3.stage3 | (intros; apply GlobalTheory.Stage3.stage3 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAlgebraisedPowersCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem cross_cancel {G : Type} [CommGroup G] (a a' g : G) (p q : ℤ) :
    (a' * g ^ q) ^ p * ((a * g ^ p) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ := by
  rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm q p]
  group

theorem lbIso_pw_cross : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  intro R _ _ I hI X hX Y β b hb hβ N v hN p q A A' hA hA' w w' hg hv hv'
  choose c hc hcg using fun e =>
    GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers X.left (Y e).left (b e) A A' (N e) p q (w e) (w' e) hA hA' (hN e) (hg e).1 (hg e).2
  refine GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions R I hI X hX Y β b hb hβ (pw A q) (pw A' p) (isLB_pw hA q) (isLB_pw hA' p) c hc ?_
  intro e z k k' hk hk'
  obtain ⟨l, hl⟩ := exists_chart (hN e) z
  obtain ⟨l', hl'⟩ := exists_chart (hN (e + 1)) (β e z)
  have hz : b (e + 1) (β e z) = b e z := by
    rw [← Scheme.Hom.comp_apply, hβ e]
  have h1 := hcg (e + 1) (Y e).left (β e) z k k' l' (hz ▸ hk) (hz ▸ hk') hl'
  have h0 := hcg e (Y e).left (𝟙 _) z k k' l hk hk' hl
  rw [h1, h0, hv e z k l' l hk hl' hl, hv' e z k' l' l hk' hl' hl]
  exact (cross_cancel _ _ _ p q).symm

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneRationalRowsSizedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_one_rational_rows_sized : Hypotheses3 → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  first | exact @GlobalTheory.Stage2.stage2 | exact GlobalTheory.Stage2.stage2 | (intros; apply GlobalTheory.Stage2.stage2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.DivP

open WithConv

variable {p : ℕ} {k : Type} [Field k]

theorem conv_eq_one_of_succ {G H : PDivGroup p k} (f : G ⟶ H) (n : ℕ) (h : f.conv (n + 1) = 1) :
    f.conv n = 1 := by
  have h1 : ∀ b, f.app (n + 1) b = algebraMap k _ (counit b) := fun b => by
    have := DFunLike.congr_fun (congrArg ofConv h) b
    simpa using this
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  change f.app n (H.res n b) = algebraMap k _ (counit (H.res n b))
  rw [← res_app, h1, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

theorem conv_eq_one_of_le {G H : PDivGroup p k} (f : G ⟶ H) {m n : ℕ} (hmn : m ≤ n)
    (h : f.conv n = 1) : f.conv m = 1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (conv_eq_one_of_succ f n h)

theorem app_kill {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) (n : ℕ) :
    ∀ {E : Type} [CommRing E] [Algebra k E] (x : G.A (n + 1) →ₐ[k] E), toConv x ^ p = 1 →
      ∀ c, x (f.app (n + 1) c) = algebraMap k E (counit c) := by
  induction n with
  | zero =>
    intro E _ _ x _ c
    have h1 : f.app 1 c = algebraMap k _ (counit c) := by
      have := DFunLike.congr_fun (congrArg ofConv hf) c
      simpa using this
    rw [h1, AlgHom.commutes]
  | succ n ih =>
    intro E _ _ x hx c
    have hx' : toConv x ^ p ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, hx, one_pow]
    obtain ⟨y, hy⟩ := (G.exists_comp_res_iff (n + 1) x).2 hx'
    have hy' : toConv y ^ p = 1 := by
      have e : pointsMap E (G.res (n + 1)) (toConv y ^ p) = 1 := by
        rw [map_pow]
        change (toConv (y.comp (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)))) ^ p = 1
        rw [hy, hx]
      apply ofConv_injective
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := G.res_surjective (n + 1) a
      have e2 := DFunLike.congr_fun (congrArg ofConv e) b
      rw [ptsMap_ofConv, AlgHom.comp_apply] at e2
      refine e2.trans ?_
      show algebraMap k E (counit b) = algebraMap k E (counit (G.res (n + 1) b))
      rw [CoalgHomClass.counit_comp_apply]
    rw [← hy, AlgHom.comp_apply]
    change y (G.res (n + 1) (f.app (n + 2) c)) = _
    rw [res_app, ih y hy', CoalgHomClass.counit_comp_apply]

theorem exists_factor [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1)
    (n : ℕ) : ∃ g : H.A (n + 1) →ₐc[k] G.A n, ∀ b, G.mulP n (g b) = f.app (n + 1) b := by
  obtain ⟨r, hrs, hrk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  rw [pow_one] at hrk
  obtain ⟨B, _, _, _, _, j, hji, hjk, hjr⟩ := GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup k (G.A (n + 1)) (G.A 1) r hrs
  have hP : kerIdeal (G.mulP n) = RingHom.ker r := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective n), mulP_comp_res, hrk]
  have h1 : ∀ a, G.mulP n a ∈ Set.range j := hjr (G.A n) (G.mulP n) hP.le
  have hmk : toConv (Ideal.Quotient.mkₐ k (torsionIdeal k (G.A (n + 1)) p)) ^ p = 1 :=
    (torsionIdeal_le_ker_iff p _).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 : ∀ b, f.app (n + 1) b ∈ Set.range j := by
    refine hjr (H.A (n + 1)) (f.app (n + 1)) ?_
    rw [hrk]
    intro a ha
    have := (kerIdeal_le_ker_iff (f.app (n + 1)) (Ideal.Quotient.mkₐ k _)).2
      (fun c => app_kill f hf n _ hmk c) ha
    rw [RingHom.mem_ker] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  let jl := (j : B →ₐ[k] G.A (n + 1)).toLinearMap
  let ml := (G.mulP n : G.A n →ₐ[k] G.A (n + 1)).toLinearMap
  have hle : LinearMap.range ml ≤ LinearMap.range jl := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := h1 a
    exact ⟨b, hb⟩
  have e1 := finrank_eq_ker_mul_range k (G.A (n + 1)) (G.A n) (G.mulP n)
  have e2 := finrank_eq_ker_mul_range k (G.A (n + 1)) B j
  rw [hP] at e1
  rw [hjk] at e2
  have hpos : 0 < Module.finrank k (G.A (n + 1) ⧸ RingHom.ker r) := by
    apply Nat.pos_of_ne_zero
    intro h0
    have : Nontrivial (G.A (n + 1)) := (counitAlgHom k (G.A (n + 1))).domain_nontrivial
    have h3 := Module.finrank_pos (R := k) (M := G.A (n + 1))
    rw [e1, h0, zero_mul] at h3
    exact lt_irrefl _ h3
  have heq : LinearMap.range ml = LinearMap.range jl :=
    Submodule.eq_of_le_of_finrank_eq hle (Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans e2))
  have h3 : ∀ b, f.app (n + 1) b ∈ Set.range (G.mulP n) := by
    intro b
    obtain ⟨c, hc⟩ := h2 b
    have : f.app (n + 1) b ∈ LinearMap.range ml := by
      rw [heq]
      exact ⟨c, hc⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective ml
    (LinearMap.ker_eq_bot.2 (Test.mulP_injective G n))
  exact GlobalTheory.bialgHom_factor_through_split k (G.A (n + 1)) (G.A n) (H.A (n + 1)) (G.mulP n) ρ
    (f.app (n + 1)) (fun a => LinearMap.congr_fun hρ a) h3

theorem exists_eq_p_smul [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  choose g' hg' using exists_factor f hf
  have hker : ∀ n, RingHom.ker (H.res n) ≤ RingHom.ker (g' n) := by
    intro n
    rw [H.ker_res]
    refine (kerIdeal_le_ker_iff _ (g' n : H.A (n + 1) →ₐ[k] G.A n)).2 fun c => ?_
    change g' n (mulBy k _ (p ^ n) c) = _
    rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]
  let gapp : ∀ n, H.A n →ₐc[k] G.A n := fun n =>
    liftSurj (H.res n) (H.res_surjective n) (g' n) (hker n)
  have hg : ∀ n b, gapp n (H.res n b) = g' n b := fun n b => liftSurj_apply ..
  have hcomm : ∀ n, (G.res n).comp (gapp (n + 1)) = (gapp n).comp (H.res n) := by
    intro n
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective (n + 1) a
    apply Test.mulP_injective G n
    change G.mulP n (G.res n (gapp (n + 1) (H.res (n + 1) b))) =
      G.mulP n (gapp n (H.res n (H.res (n + 1) b)))
    rw [hg, hg, mulP_res, hg' n, ← res_app, ← hg' (n + 1) b, res_mulP]
  refine ⟨⟨gapp, hcomm⟩, hom_ext_conv fun n => ?_⟩
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self n _)]
  have hfa : f.app n = (mulBy k (G.A n) p).comp (gapp n) := by
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective n a
    rw [← res_app, ← hg' n b, res_mulP, BialgHom.comp_apply, hg]
  change toConv (f.app n) = toConv (gapp n) ^ p
  rw [hfa, mulBy_comp, toConv_ofConv]

theorem conv_eq_one_of_p_smul [Fact p.Prime] {G H : PDivGroup p k} (g : G ⟶ H) (m : ℕ)
    (h : ((p : ℤ_[p]) • g).conv (m + 1) = 1) : g.conv m = 1 := by
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self _ _)] at h
  have h' : ∀ b, mulBy k (G.A (m + 1)) p (g.app (m + 1) b) = algebraMap k _ (counit b) := by
    intro b
    have e := DFunLike.congr_fun (congrArg ofConv h) b
    have e2 := DFunLike.congr_fun (mulBy_comp (g.app (m + 1)) p) b
    rw [BialgHom.comp_apply] at e2
    rw [e2]
    simpa using e
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective m a
  apply Test.mulP_injective G m
  change G.mulP m (g.app m (H.res m b)) = G.mulP m (algebraMap k _ (counit (H.res m b)))
  rw [← res_app, mulP_res, h', CoalgHomClass.counit_comp_apply]
  exact (AlgHomClass.commutes (G.mulP m) _).symm

theorem exists_eq_pow_smul [Fact p.Prime] {G H : PDivGroup p k} (m : ℕ) :
    ∀ f : G ⟶ H, f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  induction m with
  | zero => exact fun f _ => ⟨f, by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    intro f hf
    obtain ⟨g, rfl⟩ := exists_eq_p_smul f (conv_eq_one_of_le f (by omega) hf)
    obtain ⟨g2, rfl⟩ := ih g (conv_eq_one_of_p_smul g m hf)
    exact ⟨g2, by rw [smul_smul, ← pow_succ']⟩

theorem divisible_of_conv_eq_one : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g :=
  fun _ _ _ _ _ _ _ m f hf => exists_eq_pow_smul m f hf

end GlobalTheory.PDivGroup.DivP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModule
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem norm_natCast_padicInt (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖((n : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℤ)) := by
  rw [PadicInt.norm_def]
  push_cast
  have h := Padic.eq_padicNorm (p := l) (n : ℚ)
  push_cast at h
  rw [h, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat]
  push_cast
  rfl

theorem norm_deg_eq_norm_det : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
    ‖((deg (A := A) (B := A) f : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f hf
    obtain ⟨-, hcard⟩ := GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A f hf
    have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A) (tmap l A A f) (padicValNat l (deg f)) hcard
    change _ = ‖LinearMap.det (tmap l A A f)‖
    rw [hdet, norm_natCast_padicInt l hpos.ne']
  · have hdeg : deg (A := A) (B := A) f = 0 := by rw [deg, if_neg hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A f).2]
    have hu : IsUnit (LinearMap.det (vmap l f)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothInjectiveFamilyLiftsSmallArtinian
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem same_lift_small : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left) (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U), Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ → ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u := by
  intro R _ _ A _ g hA hgA U M hgU hfam hinj T N hN B _ _ _ I hIm hmI y u₀ h
  have key : LiftsAlong A M B I :=
    liftsAlong_of_principal R A U M (by
      intro B' _ _ _ t ht hmt
      exact GlobalTheory.DualOpen.liftsAlong_of_smooth_inj R A g hA hgA U M hgU hfam hinj B' t ht hmt) B I hIm hmI
  exact key T N hN y u₀ h

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBaseStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_identity_from_regular_base : ArCalc → RegularAlteration → GdegPull → ∀ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, SwapReg G → Swap2 G := by
  first | exact @GlobalTheory.CovTest.swap2_of_swapRegular | exact GlobalTheory.CovTest.swap2_of_swapRegular | (intros; apply GlobalTheory.CovTest.swap2_of_swapRegular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatiosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_eq_of_generic_section_ratios : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e) := by
  first | exact @GlobalTheory.Mum.thick_eq_of_ratios | exact GlobalTheory.Mum.thick_eq_of_ratios | (intros; apply GlobalTheory.Mum.thick_eq_of_ratios <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_boundary_local_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  first | exact @GlobalTheory.BdEquation.exists_reduced_equation | exact GlobalTheory.BdEquation.exists_reduced_equation | (intros; apply GlobalTheory.BdEquation.exists_reduced_equation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartsOfSiegelOfForFan
section
namespace GlobalTheory.Published

theorem toroidalCharts_of_siegel_of_forFan (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hF : GlobalTheory.Published.ToroidalChartsForFan) :
    GlobalTheory.Published.ToroidalCharts := by
  refine hF.toroidalCharts fun E _ _ _ H q => ?_
  obtain ⟨φs, hφ, -⟩ := hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitOrdersEffectiveCartierExtendFromGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitOrders_effectiveCartier_extend_from_generic : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (D : GlobalTheory.EffCartierData M.Z) (ι : ℕ), (∀ z ∈ D.idealSheaf.support, z ∉ V) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ spMap S.R.val.toRingHom ≫ u → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M V v (𝟙 F.X) T ξ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.Extend.orders_extend | exact GlobalTheory.Poinc.Extend.orders_extend | (intros; apply GlobalTheory.Poinc.Extend.orders_extend <;> assumption)
end

