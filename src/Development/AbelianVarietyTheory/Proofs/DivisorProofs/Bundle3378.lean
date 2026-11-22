import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermOfIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat.TermDescent

theorem gs_top_appLE {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) = gs φ y U a := by
  have e := gs_appLE φ U ⊤ h (𝟙 Y) y trivial a
  rwa [Category.id_comp] at e

theorem gs_of_valR {S : Type} [CommRing S] {X : Scheme.{0}} (x x' : Sp S ⟶ X) (V : X.Opens) (f : Γ(X, V))
    (c : Sˣ) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x' ⁻¹ᵁ V) (e : valR x' V f = c * valR x V f) (y : Sp S) :
    gs x' y V f = (gm (𝟙 (Sp S)) y ⊤ (unitOn c)).val * gs x y V f := by
  rw [valR, valR, dif_pos h, dif_pos h'] at e
  have e' : (x'.appLE V ⊤ h').hom f = (unitOn c).val * (x.appLE V ⊤ h).hom f := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom e
    rw [map_mul] at this
    simpa [unitOn] using this
  rw [← gs_top_appLE x' y V h', ← gs_top_appLE x y V h, e', gs_mul _ y ⊤ trivial, gs_unit _ y ⊤ trivial]

theorem gen_ratio {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {S : Type} [CommRing S] {K : Type} [Fintype K]
    {φ φ' : K → (Sp S ⟶ X)} (ε : K → ℤ) (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ c : Sˣ, ∀ y J, Good L y J →
      val t' (𝟙 _) y J = gm (𝟙 (Sp S)) y ⊤ (unitOn c) * val t (𝟙 _) y J := by
  subst e
  let u := LB.mulGen L φ ε φ (fun k => - ε k) t' (LB.invGen L φ ε t)
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ ht' (DVR.invGen_isGen _ _ _ _ ht)
  have hF : FormEq (Sum.elim φ φ) (Sum.elim ε fun k => - ε k) (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
      mul_inv_cancel, Fintype.prod_empty]
  obtain ⟨t₀, -, h₀⟩ := exists_gen hL hF u hu
  have le : (⊤ : (Sp S).Opens) ≤ LB.wchart L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let v : Γ(Sp S, ⊤)ˣ := res le (t₀.s PEmpty.elim)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v, fun y J hJ => ?_⟩
  have hv : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v) = v := by
    ext; simp [unitOn]
  have e₀ : gm (𝟙 (Sp S)) y ⊤ v = val t₀ (𝟙 _) y J :=
    (gm_res _ y le trivial _).trans (val_of t₀ _ y J PEmpty.elim fun k => k.elim).symm
  rw [hv, e₀, h₀ _ _ y J hJ, val_mul hJ, val_inv, inv_mul_cancel_right]

end GlobalTheory.Heat.TermDescent

namespace GlobalTheory.Heat
open GlobalTheory.Heat.TermDescent

theorem isTerm_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (τ : SecM Y.q.left Q.P.L k) (J : Type) (V : J → Q.P.A.left.Opens) (j : J → Fin 1 → Q.P.L.ι), ⨆ i, Y.q.left ⁻¹ᵁ V i = ⊤ → (∀ i, Y.q.left ⁻¹ᵁ V i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (j i)) → (∀ i, IsWt Y α (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i))) → ∃ σ' : Q.SecB k α, IsTerm Y k α σ' τ := by
  intro R _ _ Q O _ _ _ oa Y k α τ Jt V j hcov hle hwt
  have hL := Q.P.isLB
  obtain ⟨hs, hqc⟩ := GlobalTheory.T.ray_q_surjective_and_quasiCompact Y
  have := Ray.smooth_q Y
  let t := (Y.Φ Y.H (𝟙 _)).s α
  have ht : t.IsGen := (Y.Φ Y.H (𝟙 _)).isGen α
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Y.q.left) (DegPre.gtφT Q Y.H Y.q α))
      (Sum.elim (fun _ => (k : ℤ)) (fun a => - DegPre.gtε a)) (fun i => Y.q.left ≫ DegPre.famφB Q α i)
      (DegPre.famε k) := by
    intro U _ h
    have e := GlobalTheory.RayEv.formEq_term Y k α U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ (𝟙 _) (LB.invGen Q.P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) J, Good Q.P.L z J →
      sval σ r z J = sval τ r z J * ((val t r z J)⁻¹).val := by
    intro Z r z J hJ
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id]
    exact congrArg (fun u => sval τ r z J * u.val) (val_inv (z := z) (J := J) t r)
  have vt : ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) (y : T.left) J, Good Q.P.L y J →
      val t x.left y J = val ((Y.Φ T x).s α) (𝟙 _) y J := by
    intro T x y J hJ
    obtain ⟨-, h₂⟩ := (GlobalTheory.TorusModel.isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
    have e := h₂ α y J hJ
    rw [Category.comp_id] at e
    exact e.symm
  have hdesc : ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ Y.H.left), g₁ ≫ Y.q.left = g₂ ≫ Y.q.left →
      ∀ J, Good Q.P.L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J := by
    intro S _ _ g₁ g₂ hg J hJ
    have hA : g₂ ≫ Y.H.hom = g₁ ≫ Y.H.hom := by
      rw [← Over.w Y.q, ← Category.assoc, ← Category.assoc, hg]
    obtain ⟨φ, hφ⟩ : ∃ φ : R →+* S, g₁ ≫ Y.H.hom = spMap φ :=
      ⟨(Spec.preimage (g₁ ≫ Y.H.hom)).hom, (Spec.map_preimage _).symm⟩
    let x₁ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₁ hφ
    let x₂ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₂ (hA.trans hφ)
    have hx : x₂ ≫ Y.q = x₁ ≫ Y.q := Over.OverMorphism.ext hg.symm
    have hc : ∀ χ, ∃ c : Sˣ, ∀ y J, Good Q.P.L y J → val ((Y.Φ _ x₂).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn c) * val ((Y.Φ _ x₁).s χ) (𝟙 _) y J := fun χ =>
      gen_ratio Q.P.L hL DegPre.gtε (by rw [Ray.Φ_b, Ray.Φ_b, hx]) _ _ ((Y.Φ _ x₁).isGen χ) ((Y.Φ _ x₂).isGen χ)
    choose c hc using hc
    obtain ⟨i, hi⟩ : ∃ i, g₁ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      have : g₁ (closedPoint S) ∈ (⨆ i, Y.q.left ⁻¹ᵁ V i : Y.H.left.Opens) := by rw [hcov]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hi₂ : g₂ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      show (g₂ ≫ Y.q.left) (closedPoint S) ∈ V i
      rw [← hg]; exact hi
    have h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₁ hi).ge
    have h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₂ hi₂).ge
    have hw := hwt i S φ x₁ x₂ c g₁ g₂ rfl rfl h₁ h₂ hx hc
    have hg' := gs_of_valR g₁ g₂ _ _ (c α) h₁ h₂ hw (closedPoint S)
    have s_i : ∀ g : Sp S ⟶ Y.H.left, g (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i →
        gs g (closedPoint S) (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i)) =
          (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g (closedPoint S) (j i)
            (fun _ => J (g ≫ Y.q.left))).val * sval τ g (closedPoint S) J := by
      intro g hm
      have er : rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i) = resG _ (hle i) (τ.f (j i)) := dif_pos (hle i)
      rw [er]
      exact (gs_res g _ (hle i) hm _).trans (sec_trans τ g _ (hle i hm) (hJ.mem _ g))
    have htr : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₂ (closedPoint S) (j i)
        (fun _ => J (g₂ ≫ Y.q.left)) = trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₁ (closedPoint S) (j i)
        (fun _ => J (g₁ ≫ Y.q.left)) := by
      simp only [trF]
      rw [hg]
    set C : ((Sp S).presheaf.stalk (closedPoint S))ˣ := gm (𝟙 (Sp S)) (closedPoint S) ⊤ (unitOn (c α)) with hC
    have sv : sval τ g₂ (closedPoint S) J = C.val * sval τ g₁ (closedPoint S) J := by
      have e := hg'
      rw [s_i g₂ hi₂, s_i g₁ hi, htr, mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
    have vv : val t g₂ (closedPoint S) J = C * val t g₁ (closedPoint S) J :=
      (vt _ x₂ _ J hJ).trans ((hc α _ J hJ).trans (congrArg (C * ·) (vt _ x₁ _ J hJ).symm))
    rw [vσ _ g₁ _ J hJ, vσ _ g₂ _ J hJ, sv, vv, mul_inv_rev, Units.val_mul]
    linear_combination (-(sval τ g₁ (closedPoint S) J * ((val t g₁ (closedPoint S) J)⁻¹).val)) * C.mul_inv

  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_section_descent_flat_surjective_quasiCompact Q.P.L hL Y.q.left inferInstance hs hqc (DegPre.famφB Q α) (DegPre.famε k) σ hdesc
  refine ⟨b, fun T x y J hJ => ?_⟩
  have e1 := hb _ x.left y J hJ
  rw [vσ _ _ y J hJ, vt T x y J hJ] at e1
  show sval τ x.left y J = sval b (x.left ≫ Y.q.left) y J * _
  rw [← e1, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvWt

theorem top_le_preimage_of_fst {S : Type} [CommRing S] {X : Scheme.{0}} (w : Sp (DualNumber S) ⟶ X) (a : Sp S ⟶ X) (U : X.Opens)
    (h : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = a) (ha : ⊤ ≤ a ⁻¹ᵁ U) : ⊤ ≤ w ⁻¹ᵁ U := by
  intro p _
  let p0 : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (DualNumber S)) p
  have hp : (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) p0 = p := by
    apply PrimeSpectrum.ext
    ext z
    show algebraMap S (DualNumber S) (TrivSqZeroExt.fst z) ∈ p.asIdeal ↔ z ∈ p.asIdeal
    have hz : TrivSqZeroExt.inr (TrivSqZeroExt.snd z) ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    constructor
    · intro h1
      rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      exact p.asIdeal.add_mem h1 hz
    · intro h1
      have e : TrivSqZeroExt.inl (TrivSqZeroExt.fst z) = z - TrivSqZeroExt.inr (TrivSqZeroExt.snd z) := by
        rw [eq_sub_iff_add_eq, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
      rw [e]
      exact p.asIdeal.sub_mem h1 hz
  have hm : p0 ∈ a ⁻¹ᵁ U := ha (Set.mem_univ _)
  rw [← h] at hm
  show w p ∈ U
  rw [← hp]
  exact hm

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by
  ext
  have e := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem exists_tan_over {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    {S : Type} [CommRing S] (φ : R →+* S) :
    ∃ v' : Over.mk (spMap ((algebraMap S (DualNumber S)).comp φ)) ⟶ G,
      v'.left = spMap (dualMap φ) ≫ (tv v).left ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = (1 : Over.mk (spMap φ) ⟶ G).left := by
  refine ⟨Over.homMk (spMap (dualMap φ) ≫ (tv v).left) ?_, rfl, ?_⟩
  · rw [Category.assoc, Over.w (tv v)]
    simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
    congr 1
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp]
  · let ψ : Over.mk (spMap φ) ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) (by
        simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
        congr 1
        ext r
        simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hψ : ψ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp R)) (tm ((0 : R) • LinearMap.id)) = ψ := by
      apply Over.OverMorphism.ext
      show (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ spMap _ =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)
      simp only [spMap, ← Spec.map_comp, Category.assoc]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      simp [dualMap, CommRingCat.hom_comp, tm]
    have e := congrArg (·.left) (Formalism.L2.Pj.tan_pull (𝟙 (Sp R)) ψ hψ (tv v) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v))
    simpa [ψ] using e

theorem cv_pull_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T T' : Over (Sp R)} (k : T' ⟶ T) (x x' : T ⟶ Y.H) (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (k ≫ x')).s χ) (𝟙 _) y J =
        gm (𝟙 T'.left) y ⊤ (Units.map k.left.appTop.hom.toMonoidHom (u χ)) * val ((Y.Φ _ (k ≫ x)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have p' := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x')).2 χ y J hJ
  have p := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x)).2 χ y J hJ
  let g : LB.Gen (LB.LinComb Q.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top (u χ)⟩
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) z J', Good Q.P.L z J' → val g r z J' = gm r z ⊤ (u χ) :=
    fun Z r z J' hJ' => gm_res r z le_top (hJ'.mem PEmpty.elim r) (u χ)
  have hC := corr_of_val Q.P.isLB (t := (Y.Φ _ x').s χ) (t' := LB.mulGen Q.P.L _ _ _ _ g ((Y.Φ _ x).s χ))
    (fun y' J' hJ' => by rw [val_mul hJ', hg _ _ _ _ hJ']; exact h χ y' J' hJ')
  have e := val_corr hJ hC k.left
  rw [val_mul hJ, hg _ _ _ _ hJ] at e
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [p', p, e]
  congr 1
  have e2 := gm_pull (𝟙 _) k.left y ⊤ trivial (u χ)
  rw [Category.id_comp] at e2
  rw [← e2]
  rfl

theorem cv_mul_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T : Over (Sp R)} (X X' v : T ⟶ Y.H) (hq : X' ≫ Y.q = X ≫ Y.q)
    (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ X').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ X).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (X' * v)).s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ (X * v)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X v)).2 χ y J hJ
  have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X' v)).2 χ y J hJ
  rw [Y.Φ_b, Y.Φ_b] at h1 h2
  rw [hq] at h2
  have h3 := h χ y J hJ
  apply mul_right_cancel (b := DVR.th Q y J (DVR.cP Q _ χ) (X ≫ Y.q) (v ≫ Y.q))
  show GlobalTheory.TorusModel.cv _ χ y J * _ = _ * GlobalTheory.TorusModel.cv _ χ y J * _
  rw [h2, _root_.mul_assoc, h1, ← _root_.mul_assoc]
  congr 1

theorem _root_.GlobalTheory.Heat.IsInv.isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  intro R _ _ Q O _ _ _ oa Y v dd hinv α V f hf
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  let φε : R →+* DualNumber S := (algebraMap S (DualNumber S)).comp φ
  let π : Over.mk (spMap φε) ⟶ Over.mk (spMap φ) :=
    Over.homMk (spMap (algebraMap S (DualNumber S))) (by
      show spMap (algebraMap S (DualNumber S)) ≫ spMap φ = spMap φε
      simp only [spMap, φε, ← Spec.map_comp]; rfl)
  let ie : Over.mk (spMap φ) ⟶ Over.mk (spMap φε) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap φε = spMap φ
      simp only [spMap, φε, ← Spec.map_comp]
      congr 1)
  obtain ⟨v'', hv₁, hv₂⟩ := exists_tan_over Y.H v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hW : ∀ z : Over.mk (spMap φ) ⟶ Y.H, ie ≫ (π ≫ z * v'') = z := by
    intro z
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a := by
    rw [ha]; exact congrArg (·.left) (hW x)
  have hWa' : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x' * v'').left = a' := by
    rw [ha']; exact congrArg (·.left) (hW x')
  have htr : ∀ z : Over.mk (spMap φ) ⟶ Y.H, IsTr Y.H φ z.left v (π ≫ z * v'').left := by
    intro z
    let e : tEpsG (z.left ≫ Y.H.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ z.left ≫ Y.H.hom
      rw [Over.w z]
      simp only [Over.mk_hom, Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ z, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ z.left = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  let c' : Q.X → (DualNumber S)ˣ := fun χ => Units.map (algebraMap S (DualNumber S)).toMonoidHom (c χ)
  have hqW : (π ≫ x' * v'') ≫ Y.q = (π ≫ x * v'') ≫ Y.q := by
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, hq]
  have hcW := cv_mul_of_unit Y (π ≫ x) (π ≫ x') v'' (by rw [Category.assoc, Category.assoc, hq])
    (fun χ => Units.map π.left.appTop.hom.toMonoidHom (unitOn (c χ))) (cv_pull_of_unit Y π x x' (fun χ => unitOn (c χ)) hc)
  have key := hf (DualNumber S) φε (π ≫ x * v'') (π ≫ x' * v'') c' _ _ rfl rfl
    (top_le_preimage_of_fst _ a V hWa hV) (top_le_preimage_of_fst _ a' V hWa' hV') hqW (fun χ y J hJ => by
      rw [hcW χ y J hJ]
      congr 2
      exact map_unitOn _ _)
  have e₁ := hinv.2 S φ a (π ≫ x * v'').left V f (by rw [ha]; exact Over.w x) hV (ha ▸ htr x)
  have e₂ := hinv.2 S φ a' (π ≫ x' * v'').left V f (by rw [ha']; exact Over.w x') hV' (ha' ▸ htr x')
  rw [← e₁, ← e₂, key]
  show ((c' α : DualNumber S) * _).snd = _
  rw [TrivSqZeroExt.snd_mul]
  simp [c', TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.Heat.InvWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R)

def IsRatio {N : ℕ} {α : Q.X} (σ σ' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J

def IsRem {N : ℕ} {α : Q.X} (σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f g : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    sval σp (𝟙 _) z J = gs (𝟙 _) z U f * sval σp' (𝟙 _) z J + gs (𝟙 _) z U g * sval σ' (𝟙 _) z J

end GlobalTheory.HeatRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChartKSBracket

theorem tanPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (u : TanM (𝟙 (Sp R)) Y.H), ∃ v' : TanM (𝟙 (Sp R)) t.G, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv u)) (tv v') := by
  intro E _ _ _ H R _ _ _ _ _ t P Y u
  letI := H.starRing
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hs : spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R)) := Category.comp_id _
  obtain ⟨x, hx, -⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ (tv u))
  obtain ⟨x₀, -, hu₀⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ 1)
  have h1 := hx.pull (homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R)))) (Y.rep.1 _ _ _ (tv u))
  have e : homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) ≫ tv u = 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem u
  rw [e] at h1
  have h2 := GlobalTheory.FormalPoint.isPointOf_one P.U.toUnifPre (GlobalTheory.ExpTan.isZero_one Y.rep (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R))))
  have hk : smT (𝟙 (Sp R)) 0 x = 1 := (hu₀ _ h1).trans (hu₀ _ h2).symm
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT x hk, hx⟩

theorem isTanAtG_tv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v' : TanM (𝟙 (Sp R)) t.G), IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv v').left) := by
  intro E _ _ _ H R _ t v'
  refine GlobalTheory.LieMet.isTan_map _ ?_ (GlobalTheory.LieMet.isTan_tv v')
  rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rfl

end GlobalTheory.ChartKSBracket
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

section General

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {n : ℕ}

def combF (dd : Fin n → Fld Z) (c : Fin n → R) : Fld Z :=
  fun W f => ∑ a, constFn s W (c a) * dd a W f

def quadF (dd : Fin n → Fld Z) (M : Matrix (Fin n) (Fin n) R) : Fld Z :=
  fun W f => ∑ a, ∑ b, constFn s W (M a b) * dd a W (dd b W f)

end General

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {Ω : Type} [CommRing Ω] [StarRing Ω] [Module Ω Q.X]
  {oa : Q.OAct Ω} (Y : Ray oa)

def IsTorField (F : Fld Y.H.left) (ℓ : Q.X → R) : Prop :=
  IsField ⊤ F ∧ (∀ W r, F W (constFn Y.H.hom W r) = 0) ∧
    (∀ (α : Q.X) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f →
      F W f = constFn Y.H.hom W (ℓ α) * f) ∧
    ∀ (U : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)),
      W ≤ Y.q.left ⁻¹ᵁ U → F W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * F W f

end Raynaud

end GlobalTheory.HeatMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDataWeightVectorFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_data_weight_vector_family : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  first | exact @GlobalTheory.Stage4.stage4 | exact GlobalTheory.Stage4.stage4 | (intros; apply GlobalTheory.Stage4.stage4 <;> assumption)
end

