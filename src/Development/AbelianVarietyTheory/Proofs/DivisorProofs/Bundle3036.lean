import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatLevelOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreInjectsLevelModuleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fibre_injects_levelModule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m := by
  first | exact @GlobalTheory.EqvAct.torsLevel_pull | exact GlobalTheory.EqvAct.torsLevel_pull | (intros; apply GlobalTheory.EqvAct.torsLevel_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedUnramifiedCompleteTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fixed_unramified_complete_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.UnramTorsPull.torsion_fixed_unramified | exact GlobalTheory.UnramTorsPull.torsion_fixed_unramified | (intros; apply GlobalTheory.UnramTorsPull.torsion_fixed_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrames_sectionValues_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c → ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  first | exact @GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio | exact GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio | (intros; apply GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeRankTwo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult

namespace TorsRankTwo

open LevFlat

@[reducible] def addModule {M O : Type} [CommGroup M] [CommRing O] {ρ : O → M →* M} (h : IsAct ρ) :
    Module O (Additive M) where
  smul a x := Additive.ofMul (ρ a x.toMul)
  one_smul x := h.one x.toMul
  mul_smul a b x := by
    show ρ (a * b) x.toMul = ρ a (ρ b x.toMul)
    rw [mul_comm, h.mul]
  smul_zero a := map_one (ρ a)
  smul_add a x y := map_mul (ρ a) x.toMul y.toMul
  add_smul a b x := h.add a b x.toMul
  zero_smul x := h.zero x.toMul

theorem exists_charExp (F : Type) [Field F] [NumberField F] (N : ℕ) (Ω : Type) [Field Ω] (hN : (N : Ω) ≠ 0) :
    ∃ q : ℕ, 1 ≤ q ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 → IsCoprime 𝔭 (Ideal.span {(q : 𝓞 F)})) ∧
      ∀ b : 𝓞 F, b ≠ 0 → IsCoprime (Algebra.norm ℤ b) (q : ℤ) → ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpp | rfl
  · refine ⟨p, hpp.one_le, fun 𝔭 h𝔭 hN𝔭 => ?_, fun b _ hb h0 => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have hp𝔭 : (p : 𝓞 F) ∈ 𝔭 := by
        rw [h𝔭.eq_of_le hne le_sup_left]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      have hc : Nat.Coprime p N := hpp.coprime_iff_not_dvd.2 fun h => hN ((CharP.cast_eq_zero_iff Ω p N).2 h)
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 F))
      simp only [map_natCast] at huv
      exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ 𝔭.add_mem (𝔭.mul_mem_left u hp𝔭) (𝔭.mul_mem_left v hN𝔭)))
    · obtain ⟨u, v, huv⟩ := hb.map (Int.castRingHom Ω)
      rw [map_natCast, CharP.cast_eq_zero, eq_intCast, h0] at huv
      simp at huv
  · haveI := CharP.charP_to_charZero Ω
    refine ⟨1, le_rfl, fun 𝔭 _ _ => ?_, fun b hb _ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq, Nat.cast_one, Ideal.span_singleton_one, sup_top_eq]
    · exact Int.cast_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hb)

theorem exists_ptEquiv {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S}
    {X' : Obj F 𝔠 S'} {t : S' ⟶ S} {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X t φ) :
    ∃ e : (𝟙_ (Over S') ⟶ X'.A) ≃* (Over.mk t ⟶ X.A), ∀ x a, e (x ≫ X'.rm.act a) = e x ≫ X.rm.act a := by
  have key : ∀ t' : S' ⟶ S, (𝟙_ (Over S')).hom ≫ t = t' →
      ∃ e : (𝟙_ (Over S') ⟶ X'.A) ≃* (Over.mk t' ⟶ X.A), ∀ x a, e (x ≫ X'.rm.act a) = e x ≫ X.rm.act a := by
    rintro _ rfl
    obtain ⟨e, he⟩ := ptEquiv h.grp (𝟙_ (Over S'))
    refine ⟨e, fun x a => Over.OverMorphism.ext ?_⟩
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, h.act]
  exact key t (Category.id_comp t)

end TorsRankTwo

open LevFlat TorsRankTwo

theorem torsion_free_rank_two :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) := by
  intro F _ _ _ 𝔠 S X N Ω _ _ t hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  obtain ⟨X', φ, hφ⟩ := X.exists_isPullBy t
  obtain ⟨e, he⟩ := exists_ptEquiv hφ
  letI : Module (𝓞 F) (Additive (Over.mk t ⟶ X.A)) := addModule (isAct_ptAct X (Over.mk t))
  obtain ⟨q, hq, hq𝔭, hqb⟩ := exists_charExp F N Ω hN
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.RealMultKernel.card_ker_act_le F 𝔠 Ω X'
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.SmallNorm.exists_small_coprime_norm F q hq
  obtain ⟨p, h1, h2, h3⟩ := GlobalTheory.RankTwoTorsion.rank_two_torsion F (Additive (Over.mk t ⟶ X.A)) N
    (Nat.one_le_iff_ne_zero.2 hN0)
    (fun j => by
      rw [← GlobalTheory.abMulN_holds Ω X'.A _ (N ^ j) X'.ab X'.dim (by rw [Nat.cast_pow]; exact pow_ne_zero j hN)]
      refine Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul.trans e.symm.toEquiv) fun x => ?_)
      show x.toMul ^ (N ^ j) = 1 ↔ e.symm x.toMul ^ (N ^ j) = 1
      rw [← map_pow e.symm, e.symm.map_eq_one_iff])
    (fun 𝔭 h𝔭 hN𝔭 => ⟨C₀ * C₁ ^ 2, fun n => by
      have hI : 𝔭 ^ n ≠ ⊥ := fun h0 => by
        have := Ideal.pow_mem_pow hN𝔭 n
        rw [h0, Ideal.mem_bot] at this
        exact pow_ne_zero n (Nat.cast_ne_zero.2 hN0) this
      obtain ⟨b, hbI, hb0, hbq, k, hk, hkf⟩ := hC₁ (𝔭 ^ n) hI (hq𝔭 𝔭 h𝔭 hN𝔭).pow_left
      obtain ⟨hfin, hle⟩ := hC₀ b k (hqb b hb0 hbq) hk
      let f : {x : Additive (Over.mk t ⟶ X.A) // ∀ a ∈ 𝔭 ^ n, a • x = 0} →
          {y : 𝟙_ (Over (Sp Ω)) ⟶ X'.A // y ≫ X'.rm.act b = 1} := fun x =>
        ⟨e.symm x.1.toMul, e.injective (by
          rw [he, e.apply_symm_apply, map_one]
          exact x.2 b hbI)⟩
      have hf : Function.Injective f := fun x y hxy =>
        Subtype.ext (Additive.toMul.injective (e.symm.injective (congrArg Subtype.val hxy)))
      refine (Nat.card_le_card_of_injective f hf).trans (hle.trans ?_)
      rw [map_pow] at hkf
      calc C₀ * k ^ (2 * Module.finrank ℚ F) = C₀ * (k ^ Module.finrank ℚ F) ^ 2 := by ring
        _ ≤ C₀ * (C₁ * Ideal.absNorm 𝔭 ^ n) ^ 2 := by gcongr
        _ = C₀ * C₁ ^ 2 * Ideal.absNorm 𝔭 ^ (2 * n) := by ring⟩)
  exact ⟨fun i => (p i).toMul, h1, h2, fun y hy => h3 (Additive.ofMul y) hy⟩

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsEighthPowerProjectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_eighthPower_projections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ v : Fin 8, (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ (pG v).left → ∃ z, q.y = e q'.y v + k • z) := by
  first | exact @GlobalTheory.Poinc.Eq8.Labels.label_proj_eq | exact GlobalTheory.Poinc.Eq8.Labels.label_proj_eq | (intros; apply GlobalTheory.Poinc.Eq8.Labels.label_proj_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsPullbackUniformisationCommonFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_pullback_uniformisation_common_field : ∀ {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], IsCN V → IsCN V' → ∀ (j : V →+* V') (hj : Function.Injective j), IsLocalHom j → ∀ {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left) (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)), IsPullUnif j hD (Iso.refl _) U U' → IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j) → ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F'], (∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), QkToAkU U.toUnifPre F' k p₁ x₁ → ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧ QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left := by
  first | exact @GlobalTheory.Poinc.Sep.BaseChangeLabels.qkToAkU_pullback_common_field | exact GlobalTheory.Poinc.Sep.BaseChangeLabels.qkToAkU_pullback_common_field | (intros; apply GlobalTheory.Poinc.Sep.BaseChangeLabels.qkToAkU_pullback_common_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem GlobalTheory.Mum.Desc.lab_onto_of_labExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  intro R _ _ _ D A N hN lab F _ _ _ em lab' hext hon x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D F em N hN
  have cancel : ∀ y y' : TFK (R := R) (Kb R) ⟶ A.A, baseEm em ≫ y = baseEm em ≫ y' → y = y' := by
    intro y y' h
    apply Over.OverMorphism.ext
    exact GlobalTheory.spec_map_field_cancel em.toRingHom y.left y'.left (congrArg CommaMorphism.left h)
  have hlab : ∀ p p', QkExt em.toRingHom p p' → lab' p' = baseEm em ≫ lab p := by
    intro p p' hp
    apply Over.OverMorphism.ext
    exact hext p p' hp
  constructor
  · intro hx
    have hx' : (baseEm em ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    obtain ⟨p', hp'⟩ := (hon _).1 hx'
    obtain ⟨p, hp, -⟩ := h2 p'
    refine ⟨p, cancel _ _ ?_⟩
    rw [← hlab p p' hp, hp']
  · rintro ⟨p, rfl⟩
    obtain ⟨p', hp', -⟩ := h1 p
    have h3 := (hon (lab' p')).2 ⟨p', rfl⟩
    rw [hlab p p' hp'] at h3
    apply cancel
    rw [MonObj.comp_pow, h3, MonObj.comp_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairImageLatticePartEqOfMatchStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPairImage_latticePart_eq_of_match : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (J : Ideal V), AdmBase V J → ∀ (D₁ D₂ : DegData V J) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], Match D₁.toPre D₂.toPre b φ F → ∀ (k : ℕ) (p : QkPt D₁.toPre F k) (p' : QkPt D₂.toPre F k), Act D₁.toPre D₂.toPre b φ.symm.toAddMonoidHom p.g p'.g → p'.y = φ p.y := by
  first | exact @GlobalTheory.TInj.qImg_lattice | exact GlobalTheory.TInj.qImg_lattice | (intros; apply GlobalTheory.TInj.qImg_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEquiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif J D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → (∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x ∧ x ^ k = 1) ∧ ∀ (p p' : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x → QkPt.Equiv D.toPre F p p' := by
  first | exact @GlobalTheory.TInj.torsPt_exists_inj | exact GlobalTheory.TInj.torsPt_exists_inj | (intros; apply GlobalTheory.TInj.torsPt_exists_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointOperator_symmetricFrame_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  first | exact @GlobalTheory.Mum.Desc.phiRel_famExt | exact GlobalTheory.Mum.Desc.phiRel_famExt | (intros; apply GlobalTheory.Mum.Desc.phiRel_famExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_siegelFibre_eq_levelSection : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : S ⟶ X) (α : A.left ⟶ c.A.left), IsGrpPullback A c.A y α → ∀ (F : Type) [Field F] [IsAlgClosed F] (t : Sp F ⟶ S) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ l, x.left ≫ α = t ≫ y ≫ (c.lev l).left := by
  first | exact @GlobalTheory.TInj.torsion_isLev | exact GlobalTheory.TInj.torsion_isLev | (intros; apply GlobalTheory.TInj.torsion_isLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTorusPartEqOfEquivSameLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  first | exact @GlobalTheory.TInj.qkPt_g_eq_of_equiv | exact GlobalTheory.TInj.qkPt_g_eq_of_equiv | (intros; apply GlobalTheory.TInj.qkPt_g_eq_of_equiv <;> assumption)
end

