import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevOrbit

def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Submodule R M) (f g : M →ₗ[R] M)
    (hK : ∀ a ∈ K, f a ∈ K) (hK' : ∀ a ∈ K, g a ∈ K) (hfg : ∀ a, f (g a) - a ∈ K) (hgf : ∀ a, g (f a) - a ∈ K) :
    (M ⧸ K) ≃ₗ[R] (M ⧸ K) :=
  LinearEquiv.ofLinear (K.mapQ K f (fun a ha => hK a ha)) (K.mapQ K g (fun a ha => hK' a ha))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hfg a))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hgf a))

theorem smul_top_comap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    ∀ a ∈ (I • ⊤ : Submodule R M), f a ∈ (I • ⊤ : Submodule R M) := by
  have h : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R M).comap f := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact fun a ha => h ha

theorem exists_gam_of_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (g : Sim Dw) :
    ∃ γ : Gam Dw l₂, ∀ a, γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f l₂.M a) := by
  obtain ⟨h, hh⟩ := g.inv l₂.M (GlobalTheory.LevelFibre.level_pos l₂)
  exact ⟨quotEquiv _ (g.f l₂.M) h (smul_top_comap _ _) (smul_top_comap _ _)
    (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).2) (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).1),
    fun a => rfl⟩

theorem fibre_torsor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hA hbase lift hlift k _ _ _ _ hk y₂ y₂' y hy
  obtain ⟨hd, hM, -, -, -, hE, -, -, -⟩ := id hlev
  have hLaws : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hLaws E H Dw hpq
  refine ⟨⟨fun h' => ?_, fun ⟨γ, hγ, hr⟩ => ?_⟩, fun γ γ' h₁ h₂ => GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique E H Dw d.l₂ d.Xo₂ d.c₂ hpq hA lift hlift k y₂ y₂' γ γ' h₁ h₂⟩
  · obtain ⟨g, ρ, ν, hg, -, hmv, hfr⟩ :=
      GlobalTheory.exists_levMove_of_frOver hLaws E H Dw l Xo c 0 d hN hd hM hE d.r d.m hE k hk y y₂ y₂' hy h'
    obtain ⟨γ, hγ⟩ := exists_gam_of_sim d.l₂ g
    have hl : ∀ a, lift γ a - g.f d.l₂.M a ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
      have e := congrArg (fun f => f a) (hlift γ)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, hγ] at e
      exact (Submodule.Quotient.eq _).1 e
    refine ⟨γ, fun a => ?_, (GlobalTheory.LevelActionOfLifts.levR_congr hl y₂ y₂').2 ⟨ρ.hom, ν, inferInstance,
      ⟨hmv.1, hmv.2.1, fun a => ?_⟩, hfr⟩⟩
    · have h1 : lift γ a - g.f d.l₂.M a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
        Submodule.smul_mono_left hd.2.1 (hl a)
      have h2 := GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg a
      have := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    · have e : ∀ x x', d.Xo₂.univ.etaA x = d.Xo₂.univ.etaA x' := fun x x' => by
        have h1 := d.Xo₂.univ.etaA_ker x
        have h2 := d.Xo₂.univ.etaA_ker x'
        rw [hA, one_smul] at h1 h2
        rw [h1, h2]
      rw [e (LinearMap.id a) (g.f d.l₂.A a)]
      exact hmv.2.2 a
  · obtain ⟨ρ₂, ν₂, hi, hmv, hfr⟩ := hr
    obtain ⟨e₁, e₂⟩ := GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod E H Dw l Xo c 0 d hpq hlev hA hbase ρ₂ ν₂ (lift γ) LinearMap.id hi hmv hγ
    obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
    exact GlobalTheory.frOver_of_square_of_frMove E H Dw l Xo c 0 d (𝟙 _) ι ρ₂ ν₂ d.r d.m (by rw [e₁, Category.comp_id])
      (by rw [e₂, hι, Category.comp_id]) k y y y₂ y₂' hy (hone k y) hfr

end GlobalTheory.LevOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBis
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResLine.LeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem dual_eq {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (g : GAd σ J) (B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (e : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have h1 : adMat F (cT (σ : E →+* E) C * J) = cT (sigR (AF F) σ) (adMat F C) * adMat F J := by
    rw [c1]; exact Matrix.map_mul
  rw [h1, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← e, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (adMat F J), hu]

omit [NumberField E] in
theorem unipRad_fix {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h1 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [h1]; simp⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [Subgroup.mem_bot.1 hB] at e
  simpa using e

variable {X Y : Matrix (Fin n) (Fin r) E}

theorem mem_unipRad_iff (hW : IsWittFrame σ J X Y) (k : Fin r) (g : GAd σ J) :
    g ∈ unipRad σ J (initCols X k) ↔ (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) ∧
      ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 →
        ∃ a, adMat F (initCols X k) *ᵥ a = (matHom _ σ J g).1 *ᵥ y - y := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  refine ⟨fun hg => ⟨unipRad_fix hg, fun y hy => ?_⟩, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [← unip_singleton hW] at hg
    have := hg.2.2 y (by rw [e1, mem_colPerp_iff]; exact hy)
    rwa [e1, mem_colSpan_iff] at this
  · rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  · have := dual_eq (initCols X k) g 1 (by rw [h1, Matrix.mul_one])
    rw [Formalism.UG.cT_one, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  · have := h2 (fun i => inclR (F := F) (AF F) (x i)) (by
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

theorem conj_mem (hW : IsWittFrame σ J X Y) (k : Fin r) {m u : GAd σ J} (hm : m ∈ frameStab σ J (initCols X k) ⊤)
    (hu : u ∈ unipRad σ J (initCols X k)) : m * u * m⁻¹ ∈ unipRad σ J (initCols X k) := by
  rw [mem_unipRad_iff hW] at hu ⊢
  obtain ⟨B', -, e'⟩ := inv_mem hm
  obtain ⟨B, -, e⟩ := hm
  have hmm : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, e', ← Matrix.mul_assoc (Units.val _) _ B'.1,
      hu.1, ← e', ← Matrix.mul_assoc, hmm, Matrix.one_mul]
  · have hd := dual_eq (initCols X k) m B.1 e
    obtain ⟨a, ha⟩ := hu.2 ((matHom _ σ J m⁻¹).1 *ᵥ y) (by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc, hmm, Matrix.mul_one, ← mulVec_mulVec, hy, mulVec_zero])
    refine ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, ← e, ← mulVec_mulVec, ha, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmm, one_mulVec,
      map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem eq_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (k : Fin r) {g : GAd σ J}
    (hg : g ∈ unipRad σ J (initCols X k)) (hm : g ∈ frameStab σ J (initCols Y k) ⊤) : g = 1 := by
  rw [mem_unipRad_iff hW] at hg
  obtain ⟨B, -, e⟩ := hm
  have hT : cT (σ : E →+* E) (initCols X k) * J * initCols Y k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have hT' : cT (σ : E →+* E) (initCols Y k) * J * initCols X k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have aT : adMat F (cT (σ : E →+* E) (initCols X k) * J) * adMat F (initCols Y k) = 1 := by
    rw [← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _)]
  have aT' : adMat F (cT (σ : E →+* E) (initCols Y k) * J) * adMat F (initCols X k) = 1 := by
    rw [← Matrix.map_mul, hT', Matrix.map_one _ (map_zero _) (map_one _)]
  have d1 := dual_eq (initCols X k) g 1 (by rw [hg.1, Matrix.mul_one])
  rw [Formalism.UG.cT_one, Matrix.one_mul] at d1
  have hB : B.1 = 1 := by
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols X k) * J) * ·) e
    simp only [← Matrix.mul_assoc] at this
    rw [d1, aT, Matrix.one_mul] at this
    exact this.symm
  have d2 := dual_eq (initCols Y k) g _ e
  rw [hB, Formalism.UG.cT_one, Matrix.one_mul] at d2
  rw [hB, Matrix.mul_one] at e
  have h0 : ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 → (matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    obtain ⟨a, ha⟩ := hg.2 y hy
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols Y k) * J) *ᵥ ·) ha
    simp only [mulVec_mulVec, mulVec_sub] at this
    rw [aT', d2, sub_self, one_mulVec] at this
    rw [this, mulVec_zero] at ha
    exact sub_eq_zero.1 ha.symm
  have h1 : ∀ y, (matHom _ σ J g).1 *ᵥ y = y := fun y => by
    have := h0 (y - adMat F (initCols Y k) *ᵥ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y) (by
      rw [mulVec_sub, mulVec_mulVec (M := adMat F (cT (σ : E →+* E) (initCols X k) * J)), aT, one_mulVec, sub_self])
    rw [mulVec_sub, mulVec_mulVec (M := (matHom _ σ J g).1), e] at this
    exact sub_left_injective this
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := h1 (Pi.single j 1)
  rw [mulVec_single_one] at this
  exact (congrFun this i).trans (Pi.single_apply _ _ _)

theorem mul_one_by_one {R : Type} [CommRing R] (C : Matrix (Fin n) (Fin 1) R) (B : Matrix (Fin 1) (Fin 1) R) :
    C * B = B.det • C := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

theorem absE_of_scales {x : Matrix (Fin n) (Fin 1) E} {L : Matrix (Fin 1) (Fin n) E} (hL : L * x = 1) {γ : GAd σ J}
    (hγ : γ ∈ ratPts σ J) {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x γ l) : absE F E l = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F x = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : E := (L * γ0.1.1 * x) 0 0 with hc
  have hl : l.1 = inclR (F := F) (AF F) c := by
    have := congrArg (adMat F L * ·) e
    simp only [Matrix.mul_smul] at this
    rw [hL', hmat, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul] at this
    have := congrFun (congrFun this 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this.symm
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := l.mul_inv
      rw [hl, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim l 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = l from
      Units.ext (by simp [hl])] at this

theorem levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y →
    (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (ResLine.col X), m * u * m⁻¹ ∈ unipRad σ J (ResLine.col X)) ∧
    (∀ g ∈ unipRad σ J (ResLine.col X), g ∈ levi σ J X Y {0} → g = 1) ∧
    (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧
    (∀ u ∈ unipRad σ J (ResLine.col X), Scales σ J (ResLine.col X) u 1) ∧
    (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (ResLine.col X) m l ∧ absE F E l = 1) ∧
    ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (ResLine.col X) γ l → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hc : ResLine.col X = initCols X 0 := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  have hlev : ∀ m ∈ levi σ J X Y {0}, m ∈ frameStab σ J (initCols X 0) ⊤ ∧ m ∈ frameStab σ J (initCols Y 0) ⊤ :=
    fun m hm => by
      simp only [levi, Subgroup.mem_iInf] at hm
      exact hm 0 (Finset.mem_singleton_self _)
  have hT' : cT (σ : E →+* E) (initCols Y 0) * J * initCols X 0 = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE (0 : Fin (r + 1)).2)) (j.castLE (0 : Fin (r + 1)).2)).trans
      (by simp only [Matrix.one_apply, Fin.castLE_inj])
  have h6 : ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (initCols X 0) γ l → absE F E l = 1 := fun γ hγ l e =>
    absE_of_scales hT' hγ e
  rw [hc]
  refine ⟨fun m hm u hu => conj_mem hW 0 (hlev m hm).1 hu, fun g hg hm => eq_one h hJ hW 0 hg (hlev g hm).2,
    fun γ hγ hm => ⟨hm, ?_⟩, fun u hu => ?_, fun m hm => ?_, h6⟩
  · show γ ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker
    simp only [Subgroup.mem_iInf]
    intro k hk
    obtain rfl := Finset.mem_singleton.1 hk
    obtain ⟨B, -, e⟩ := (hlev γ hm).1
    exact ⟨B, h6 γ hγ (Matrix.GeneralLinearGroup.det B) (e.trans (mul_one_by_one _ _)), e⟩
  · exact (unipRad_fix hu).trans (one_smul _ _).symm
  · have h2 : m ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
    simp only [Subgroup.mem_iInf] at h2
    obtain ⟨B, hB, e⟩ := h2 0 (Finset.mem_singleton_self _)
    exact ⟨Matrix.GeneralLinearGroup.det B, e.trans (mul_one_by_one _ _), hB⟩

end GlobalTheory.ResLine.LeviFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

theorem exists_ext (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    ∃ τ' : F →+* ℂ, ∀ c : 𝓞 F, τ' (c : F) = τ c := by
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker τ) hne (by simpa [RingHom.mem_ker] using hx)
      (Algebra.IsIntegral.isIntegral x)
    apply hI
    rw [eq_bot_iff]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, map_intCast] at hn
    simpa using hn
  refine ⟨IsFractionRing.lift hinj, fun c => ?_⟩
  exact IsFractionRing.lift_algebraMap hinj c

theorem root_cases {r z : ℂ} {tr nm : ℤ} (hd : tr ^ 2 - 4 * nm < 0) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (z ≠ r ↔ (starRingEnd ℂ) z = r) := by
  have hc : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hfac : ∀ x : ℂ, x ^ 2 - tr * x + nm = 0 → x = r ∨ x = tr - r := by
    intro x hx
    have : (x - r) * (x - (tr - r)) = 0 := by linear_combination hx - hr
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    have him : r.im = 0 := Complex.conj_eq_iff_im.1 h
    have hre := congrArg Complex.re hr
    have himr : r = (r.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [himr] at hre
    simp [sq] at hre
    have : ((2 * r.re - tr) ^ 2 : ℝ) = (tr : ℝ) ^ 2 - 4 * nm := by linear_combination 4 * hre
    have h2 : ((tr : ℝ) ^ 2 - 4 * nm) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * r.re - tr)]
  have hcr : (starRingEnd ℂ) r = tr - r := (hfac _ hc).resolve_left hne
  constructor
  · intro h
    have : z = tr - r := (hfac z hz).resolve_left h
    rw [this, ← hcr]; simp
  · intro h hzr
    rw [hzr] at h
    exact hne h

theorem lie_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  intro p _ D R _ b N σ ρ o h hL D' t Q e hU
  classical
  choose τ hτ using fun i => exists_ext D.F (σ.comp (b.t i))
  have hτ' : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c => hτ i c
  obtain ⟨hrank, hcov⟩ := GlobalTheory.T.eigenspace_dimension_of_uniformization p D R b N σ ρ o h hL D' t Q e hU τ hτ'
  have hsum := GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul p D D' ρ Q hU.2.1
  set r := σ b.ρ with hrdef
  have hr : r ^ 2 - D.tr * r + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hω : (D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hτω : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have := congrArg (fun x : 𝓞 D.F => τ' (x : D.F)) hω
    simpa using this
  have key : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ≠ r ↔ ((starRingEnd ℂ).comp τ') (D.ω : D.F) = r :=
    fun τ' => root_cases D.disc_neg hr (hτω τ')

  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have h1 := hτ' i x
      have h2 := hτ' j x
      rw [hij] at h1
      simp [RingHom.mem_ker, ← h1, ← h2]
    rw [b.comax i j hne] at hle
    have : (1 : R) ∈ RingHom.ker σ := hle Submodule.mem_top
    simp [RingHom.mem_ker] at this
  have hτA : ∀ i, τ i (D.ω : D.F) = r := fun i => by rw [hτ', b.t_ω]
  set d : (D.F →+* ℂ) → ℕ := fun τ' => Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ') with hd

  have hzero : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = r → τ' ∉ Finset.univ.image τ → d τ' = 0 := by
    intro τ' h1 h2
    have hbot : eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ' = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = r • u := by
        have := hu D.ω
        rw [h1] at this
        exact this
      have hmem := hcov u hu'
      have hle : (⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) ≤ ⨆ τ'' ∈ Finset.univ.image τ, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'' := by
        refine iSup_le fun i => ?_
        exact le_biSup (fun τ'' => eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'') (Finset.mem_image_of_mem τ (Finset.mem_univ i))
      have := (GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) _ τ' h2).le_bot ⟨hu, hle hmem⟩
      simpa using this
    simp [hd, hbot]
  have hA : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ i, (D.m : ℂ) * σ (b.t i c) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hA' : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) =
      ∑ i, (D.m : ℂ) * (starRingEnd ℂ) (σ (b.t i c)) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hconj : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) := by
    intro c
    refine Finset.sum_nbij' (fun τ' => (starRingEnd ℂ).comp τ') (fun τ' => (starRingEnd ℂ).comp τ') ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have := (key x).1 (by simpa using hx)
      simpa using this
    · intro x hx
      have hx' : x (D.ω : D.F) = r := by simpa using hx
      have : ¬ ((starRingEnd ℂ).comp x) (D.ω : D.F) = r := by
        exact fun h => (key x).2 h hx'
      simpa using this
    · intro x _; ext; simp
    · intro x _; ext; simp
    · intro x _; simp
  intro c
  have htr : (ρ (algebraMap (𝓞 D.F) D.O c)).trace = ∑ τ' : D.F →+* ℂ, (d τ' : ℂ) * τ' (c : D.F) := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) c
  rw [htr, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r)]
  have hB : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), ((D.m : ℂ) * D.n * τ' (c : D.F) -
        (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F)) := by
    refine Finset.sum_congr rfl fun τ' _ => ?_
    have := hsum τ'
    have h' : (d τ' : ℂ) + d ((starRingEnd ℂ).comp τ') = D.m * D.n := by exact_mod_cast this
    linear_combination τ' (c : D.F) * h'
  rw [hB, Finset.sum_sub_distrib, hconj c, hA c, hA' c]
  have e1 : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.m : ℂ) * D.n * τ' (c : D.F) =
      D.m * ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.n : ℂ) * τ' (c : D.F) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  simp only [← Finset.mul_sum]
  ring

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjEqOfWitness
section
open MeasureTheory

namespace GlobalTheory.ConjugationEquivalence

def conjEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * u * b⁻¹, (h u).1 u.2⟩
  invFun u := ⟨b⁻¹ * u * b, (h _).2 (by simpa [mul_assoc] using u.2)⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

end GlobalTheory.ConjugationEquivalence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStepStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_filtration_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | exact GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | (intros; apply GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReadingStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedSection_reading_eq_movedFrame_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  first | exact @GlobalTheory.GeoLevel.rdU_move_eq | exact GlobalTheory.GeoLevel.rdU_move_eq | (intros; apply GlobalTheory.GeoLevel.rdU_move_eq <;> assumption)
end

