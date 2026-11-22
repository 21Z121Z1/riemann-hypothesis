import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0680
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdEvalTruncOfHighOrderStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_dvd_eval_trunc_of_high_order : ∀ (p : ℕ) (B : Type) [CommRing B] (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∃ L : ℕ, ∀ (k : ℕ) (h : MvPowerSeries σ B), (∀ α : σ →₀ ℕ, α.degree < L * k → coeff α h = 0) → ∀ n : σ →₀ ℕ, (p : B) ^ k ∣ MvPolynomial.eval z (trunc' B n h) := by
  first | exact @GlobalTheory.trunc'_eval_dvd_of_order | exact GlobalTheory.trunc'_eval_dvd_of_order | (intros; apply GlobalTheory.trunc'_eval_dvd_of_order <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModIntStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B), (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) → ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  first | exact @GlobalTheory.FrobStep.frob_comb_step | exact GlobalTheory.FrobStep.frob_comb_step | (intros; apply GlobalTheory.FrobStep.frob_comb_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormalStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog : ∀ (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q), constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  first | exact @GlobalTheory.FormalCalc.lin_formalLog | exact GlobalTheory.FormalCalc.lin_formalLog | (intros; apply GlobalTheory.FormalCalc.lin_formalLog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine GlobalTheory.T.structureSheafCohomology_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveOfAxesVanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_of_axes_vanishing : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 | exact GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 | (intros; apply GlobalTheory.AbCoh.PrimLift.primO1_of_axesO1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEqZeroOfSuccLe
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem prod_eq_zero_of_succ_le {I : Type} {D : Type} [CommRing D] (N : ℕ) (t : I → D)
    (h : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (k : ℕ) (hk : N + 1 ≤ k) (s : Fin k → I) :
    ∏ a, t (s a) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, h (fun a => s (Fin.castAdd j a)), zero_mul]

theorem taylor_eq_of_le : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (N' : ℕ), N ≤ N' → ∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N' t f = GlobalTheory.PeriodFamily.taylor N t f := by
  intro I _ _ D _ _ N t h N' hN f
  induction N', hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    unfold taylor
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [prod_eq_zero_of_succ_le N t h (n + 1) (by omega)]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvdStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M), (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  first | exact @GlobalTheory.projective_dvd_of_forall_dual_dvd | exact GlobalTheory.projective_dvd_of_forall_dual_dvd | (intros; apply GlobalTheory.projective_dvd_of_forall_dual_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjective
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem isNilpotent_matrix_of_entries_mem {R : Type*} [CommRing R] {n : ℕ} (I : Ideal R) (N : ℕ)
    (hN : I ^ N = ⊥) (M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, M i j ∈ I) : IsNilpotent M := by
  have key : ∀ j : ℕ, ∀ a b, (M ^ j) a b ∈ I ^ j := by
    intro j
    induction j with
    | zero => intro a b; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ j ih =>
      intro a b
      rw [pow_succ M, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hM c b)
  refine ⟨N, ?_⟩
  ext a b
  have := key N a b
  rw [hN, Ideal.mem_bot] at this
  simpa using this

theorem le_pow_smul_of_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (K : Submodule R M) (hK : K ≤ I • K) (j : ℕ) : K ≤ (I ^ j) • K := by
  induction j with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  | succ j ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact hK.trans (Submodule.smul_mono le_rfl ih)

end GlobalTheory.HTSummand

namespace GlobalTheory.HTSummand

theorem projective_tensor_of_fibre_projective :
    ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k),
      Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V]
      (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H →
      Module.Projective C H → Function.Surjective f →
      (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) →
      (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) →
      letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  intro C k B _ _ _ _ _ σ hσ H V _ _ _ _ ρ ρ' f hfin hproj hf hker hcomm hV
  letI mH : Module (C ⊗[ℤ] B) H := tensorModOf ρ
  letI mV : Module (k ⊗[ℤ] B) V := tensorModOf ρ'

  set m : Ideal C := RingHom.ker σ with hm_def
  have hmtop : m ≠ ⊤ := by
    intro h
    have : (1 : C) ∈ m := h ▸ Submodule.mem_top
    rw [hm_def, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have hmjac : m ≤ (⊥ : Ideal C).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hmtop
  obtain ⟨N, hN⟩ : ∃ N : ℕ, m ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    exact ⟨N, le_bot_iff.1 ((Ideal.pow_right_mono hmjac N).trans (le_of_eq hN))⟩

  let τa := Algebra.TensorProduct.map σ.toIntAlgHom (AlgHom.id ℤ B)
  let τ : C ⊗[ℤ] B →+* k ⊗[ℤ] B := τa.toRingHom
  have hτ : Function.Surjective τ :=
    Algebra.TensorProduct.map_surjective σ.toIntAlgHom (AlgHom.id ℤ B) hσ Function.surjective_id
  have hτtmul : ∀ (c : C) (b : B), τ (c ⊗ₜ b) = σ c ⊗ₜ b := fun _ _ => rfl
  have hkerτ : RingHom.ker τ ≤ Ideal.map (algebraMap C (C ⊗[ℤ] B)) m := by
    have h1 : RingHom.ker τ = Ideal.map Algebra.TensorProduct.includeLeft m :=
      Algebra.TensorProduct.rTensor_ker σ.toIntAlgHom hσ
    rw [h1]
    exact Ideal.map_le_iff_le_comap.2 fun c hc => Ideal.mem_map_of_mem (algebraMap C (C ⊗[ℤ] B)) hc
  have hJm : ∀ x ∈ RingHom.ker τ, x ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) := by
    intro x hx
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact hkerτ hx
  have hJN : (RingHom.ker τ) ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.pow_right_mono hkerτ N).trans ?_)
    rw [← Ideal.map_pow, hN, Ideal.map_bot]

  haveI tC : IsScalarTower C (C ⊗[ℤ] B) H := IsScalarTower.of_algebraMap_smul fun c h => by
    show ((c ⊗ₜ[ℤ] (1 : B) : C ⊗[ℤ] B)) • h = c • h
    rw [tensorModOf_tmul, map_one]
    rfl
  letI mRV : Module (C ⊗[ℤ] B) V := Module.compHom V τ
  let fR : H →ₗ[C ⊗[ℤ] B] V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r h => by
        show f (r • h) = τ r • f h
        induction r using TensorProduct.induction_on with
        | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
        | tmul c b =>
          rw [hτtmul, tensorModOf_tmul, tensorModOf_tmul, f.map_smulₛₗ, hcomm]
        | add x y hx hy => rw [add_smul, map_add, hx, hy, map_add, add_smul] }
  have hfR : Function.Surjective fR := hf
  haveI : Module.Finite (C ⊗[ℤ] B) H := Module.Finite.of_restrictScalars_finite C (C ⊗[ℤ] B) H
  haveI : Module.Finite (C ⊗[ℤ] B) V := Module.Finite.of_surjective fR hfR
  haveI finSV : Module.Finite (k ⊗[ℤ] B) V := by
    letI : Algebra (C ⊗[ℤ] B) (k ⊗[ℤ] B) := τ.toAlgebra
    haveI : IsScalarTower (C ⊗[ℤ] B) (k ⊗[ℤ] B) V := IsScalarTower.of_algebraMap_smul fun r v => rfl
    exact Module.Finite.of_restrictScalars_finite (C ⊗[ℤ] B) (k ⊗[ℤ] B) V

  obtain ⟨n, pb, hpb⟩ := Module.Finite.exists_fin' (k ⊗[ℤ] B) V
  obtain ⟨sb, hsb⟩ := Module.projective_lifting_property pb LinearMap.id hpb
  have hps : ∀ v, pb (sb v) = v := fun v => LinearMap.congr_fun hsb v
  set eb : Matrix (Fin n) (Fin n) (k ⊗[ℤ] B) := LinearMap.toMatrix' (sb ∘ₗ pb) with heb
  have heb_idem : IsIdempotentElem eb := by
    show eb * eb = eb
    rw [heb, ← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, hps]
  have heb_apply : ∀ y, eb.mulVec y = sb (pb y) := fun y => by
    rw [heb, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  obtain ⟨E, hE, hEeb⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (τ.mapMatrix :
      Matrix (Fin n) (Fin n) (C ⊗[ℤ] B) →+* Matrix (Fin n) (Fin n) (k ⊗[ℤ] B))
    (fun x hx => by
      refine isNilpotent_matrix_of_entries_mem (RingHom.ker τ) N hJN x fun i j => ?_
      rw [RingHom.mem_ker] at hx ⊢
      exact congrFun (congrFun hx i) j)
    eb ⟨eb.map (Function.surjInv hτ), by ext i j; simp [Function.surjInv_eq hτ]⟩ heb_idem
  have hEE : ∀ w, E.mulVec (E.mulVec w) = E.mulVec w := fun w => by
    rw [Matrix.mulVec_mulVec, hE.eq]
  have hτE : ∀ w : Fin n → C ⊗[ℤ] B, (fun i => τ (E.mulVec w i)) = sb (pb (fun i => τ (w i))) := by
    intro w
    rw [← heb_apply, ← hEeb]
    funext i
    exact RingHom.map_mulVec τ E w i

  set Q : Submodule (C ⊗[ℤ] B) (Fin n → C ⊗[ℤ] B) := LinearMap.range (Matrix.toLin' E) with hQ
  have hQE : ∀ q : Q, E.mulVec (q : Fin n → C ⊗[ℤ] B) = q := by
    rintro ⟨q, w, rfl⟩
    show E.mulVec (Matrix.toLin' E w) = Matrix.toLin' E w
    rw [Matrix.toLin'_apply, hEE]
  let sQ : (Fin n → C ⊗[ℤ] B) →ₗ[C ⊗[ℤ] B] Q :=
    (Matrix.toLin' E).codRestrict Q fun w => LinearMap.mem_range_self _ w
  have hsQ : ∀ q : Q, sQ q = q := fun q => Subtype.ext (by
    show Matrix.toLin' E (q : Fin n → C ⊗[ℤ] B) = q
    rw [Matrix.toLin'_apply, hQE])
  haveI hQproj : Module.Projective (C ⊗[ℤ] B) Q :=
    Module.Projective.of_split Q.subtype sQ (LinearMap.ext hsQ)
  let φ : Q →ₗ[C ⊗[ℤ] B] V :=
    { toFun := fun q => pb (fun i => τ ((q : Fin n → C ⊗[ℤ] B) i))
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        funext i
        simp
      map_smul' := fun r x => by
        show pb _ = τ r • pb _
        rw [← map_smul]
        congr 1
        funext i
        simp }
  have hφ : Function.Surjective φ := by
    intro v
    let w : Fin n → C ⊗[ℤ] B := fun i => Function.surjInv hτ (sb v i)
    refine ⟨⟨Matrix.toLin' E w, LinearMap.mem_range_self _ w⟩, ?_⟩
    show pb (fun i => τ (Matrix.toLin' E w i)) = v
    rw [Matrix.toLin'_apply, hτE]
    have : (fun i => τ (w i)) = sb v := funext fun i => Function.surjInv_eq hτ _
    rw [this, hps, hps]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property fR φ hfR
  have hgφ : ∀ q, f (g q) = φ q := fun q => LinearMap.congr_fun hg q

  have hgs : Function.Surjective g := by
    have hle : (⊤ : Submodule C H) ≤ (LinearMap.range g).restrictScalars C ⊔ m • ⊤ := by
      intro h _
      obtain ⟨q, hq⟩ := hφ (f h)
      have h0 : f (h - g q) = 0 := by rw [map_sub, hgφ, hq, sub_self]
      have : h = g q + (h - g q) := by abel
      rw [this]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self g q) (hker _ h0)
    have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hmjac hle
    intro h
    exact htop Submodule.mem_top

  let g' : Q →ₗ[C] H := g.restrictScalars C
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g' LinearMap.id hgs
  have hgs' : ∀ h, g' (s h) = h := fun h => LinearMap.congr_fun hs h
  let P : Q →ₗ[C] Q := LinearMap.id - s ∘ₗ g'
  have hPK : ∀ x, P x ∈ LinearMap.ker g' := fun x => by
    rw [LinearMap.mem_ker]
    show g' (x - s (g' x)) = 0
    rw [map_sub, hgs', sub_self]
  have hKm : ∀ x ∈ LinearMap.ker g', x ∈ (m • ⊤ : Submodule C Q) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hφx : φ x = 0 := by rw [← hgφ]; exact (congrArg f hx).trans (map_zero f)
    have hτx : (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := by
      have h1 := hτE x
      rw [hQE x] at h1
      rw [h1]
      have : pb (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := hφx
      rw [this, map_zero]
    have hx1 : (x : Fin n → C ⊗[ℤ] B) ∈ (m • ⊤ : Submodule C (Fin n → C ⊗[ℤ] B)) := by
      rw [← Finset.univ_sum_single (x : Fin n → C ⊗[ℤ] B)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : (x : Fin n → C ⊗[ℤ] B) i ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) :=
        hJm _ (RingHom.mem_ker.2 (congrFun hτx i))
      have := Submodule.mem_map_of_mem (f := LinearMap.single C (fun _ : Fin n => C ⊗[ℤ] B) i) hi
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have := Submodule.mem_map_of_mem (f := sQ.restrictScalars C) hx1
    rw [Submodule.map_smul''] at this
    have hx' : sQ.restrictScalars C x = x := hsQ x
    rw [hx'] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hK : LinearMap.ker g' ≤ m • LinearMap.ker g' := by
    intro x hx
    have hPx : P x = x := by
      show x - s (g' x) = x
      rw [LinearMap.mem_ker.1 hx, map_zero, sub_zero]
    have := Submodule.mem_map_of_mem (f := P) (hKm x hx)
    rw [Submodule.map_smul'', hPx] at this
    exact Submodule.smul_mono le_rfl (fun y hy => by
      obtain ⟨z, _, rfl⟩ := hy
      exact hPK z) this
  have hK0 : LinearMap.ker g' = ⊥ := by
    have := le_pow_smul_of_le_smul m _ hK N
    rw [hN, Submodule.bot_smul] at this
    exact le_bot_iff.1 this
  have hgi : Function.Injective g := by
    have h' : Function.Injective g' := LinearMap.ker_eq_bot.1 hK0
    exact h'
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective g ⟨hgi, hgs⟩)

end GlobalTheory.HTSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantValuationBound
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem log_val_lead_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ τ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → Real.log (v (c τ)) = N * κ₀ + ∑ᶠ σ, (a σ : ℝ) * κ σ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ τ
  classical
  haveI : Finite (Λ →+* O) := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  let S : Set (Option (Λ →+* O) → ℕ) := {x | ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C),
    IsDetElt ε ψ (x none) Δ ∧ HasOrders C ε (x none) Δ (fun σ => x (some σ)) c}
  let F : (Option (Λ →+* O) → ℕ) → ℝ := fun x =>
    if h : x ∈ S then Real.log (v (Classical.choose (Classical.choose_spec h) τ)) else 0
  have hF : ∀ x (h : x ∈ S) (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ (x none) Δ →
      HasOrders C ε (x none) Δ (fun σ => x (some σ)) c → F x = Real.log (v (c τ)) := by
    intro x h Δ c h1 h2
    simp only [F, dif_pos h]
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (Classical.choose_spec h)
    rw [GlobalTheory.T.psi_determinant_eigen_property p C v O hv ε hε Λ ψ hψ (x none) _ Δ _ _ c h1' h1 h2' h2 τ]
  obtain ⟨f, hf, -⟩ := theta_tensor_exists p C v O hv ε hε Λ τ
  have hne : ∀ N (Δ : RL p O Λ) a (c : (Λ →+* O) → C), HasOrders C ε N Δ a c →
      ((v (c τ) : NNReal) : ℝ) ≠ 0 := fun N Δ a c h =>
    NNReal.coe_ne_zero.2 ((Valuation.ne_zero_iff v).2 (h τ f hf).2.1)
  obtain ⟨κ', hκ'⟩ := GlobalTheory.T.additive_function_on_monoid_linear (Option (Λ →+* O)) S F (by
    rintro x ⟨Δ, c, h1, h2⟩ y ⟨Δ', c', h1', h2'⟩
    obtain ⟨k1, k2⟩ := GlobalTheory.T.determinant_element_product p O C ε Λ ψ _ _ Δ Δ' _ _ c c' h1 h1' h2 h2'
    have hxy : x + y ∈ S := ⟨Δ * Δ', c * c', k1, k2⟩
    refine ⟨hxy, ?_⟩
    rw [hF _ hxy _ _ k1 k2, hF x ⟨Δ, c, h1, h2⟩ _ _ h1 h2, hF y ⟨Δ', c', h1', h2'⟩ _ _ h1' h2',
      Pi.mul_apply, map_mul, NNReal.coe_mul, Real.log_mul (hne _ _ _ _ h2) (hne _ _ _ _ h2')])
  refine ⟨κ' none, fun σ => κ' (some σ), ?_⟩
  intro N Δ a c h1 h2
  let x : Option (Λ →+* O) → ℕ := fun o => o.elim N a
  have hx : x ∈ S := ⟨Δ, c, h1, h2⟩
  rw [← hF x hx Δ c h1 h2, hκ' x hx, Fintype.sum_option, finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibreStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_h1_surjective_bijective_fibre : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveOfBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective_base : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) :=
  fun R R' _ _ σ X X' s s' φ h hσ ↦ pullHO1_surjective_of_bijective R R' σ hσ X s X' s' φ h

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverseStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  first | exact @GlobalTheory.BasisTrans.trans_inverse | exact GlobalTheory.BasisTrans.trans_inverse | (intros; apply GlobalTheory.BasisTrans.trans_inverse <;> assumption)
end

