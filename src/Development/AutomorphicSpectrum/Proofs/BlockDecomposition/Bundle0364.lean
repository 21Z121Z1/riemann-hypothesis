import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0308
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistedSectionsApproximationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twisted_sections_approximation : UniformGen → ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.step_uniform | exact GlobalTheory.CompanionTheory.GE.Step.step_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.Step.step_uniform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorizationStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  first | exact @GlobalTheory.CompanionTheory.DCell.main | exact GlobalTheory.CompanionTheory.DCell.main | (intros; apply GlobalTheory.CompanionTheory.DCell.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (u + ((r : ℂ) - 1) / 2)

def capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (u + ((s : ℂ) - 1) / 2)

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLower
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem lowC_central_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro k _ _ _ _ n s d e U hU
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k), Units.val ⁻¹' V ⊆ U := by
    rw [(isEmbedding_val_GL (k := k) n).nhds_eq_comap] at hU
    simpa using Filter.mem_comap.mp hU
  obtain ⟨W, hW, hWV⟩ := exists_entry_nhds hV
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).mp hW
  obtain ⟨c, hc0, hcγ, hc1⟩ : ∃ c : k, c ≠ 0 ∧ ValuativeRel.valuation k c < γ ∧
      ValuativeRel.valuation k c ≤ 1 := by
    obtain ⟨x, hx0, hx1⟩ := (Valuation.IsNontrivial.exists_lt_one : ∃ x : k, x ≠ 0 ∧ ValuativeRel.valuation k x < 1)
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := k) (γ : ValuativeRel.ValueGroupWithZero k)
    have hy0 : (0 : ValuativeRel.ValueGroupWithZero k) < ValuativeRel.valuation k y := by
      rw [hy]; exact Units.zero_lt γ
    rcases le_or_gt (ValuativeRel.valuation k y) 1 with hy1 | hy1
    · refine ⟨y * x, ?_, ?_, ?_⟩
      · exact mul_ne_zero (by rintro rfl; simp at hy0) hx0
      · rw [map_mul, ← hy]; exact mul_lt_of_lt_one_right hy0 hx1
      · rw [map_mul]; first | exact mul_le_one' hy1 hx1.le | exact mul_le_one₀ hy1 zero_le' hx1.le
    · refine ⟨x, hx0, ?_, hx1.le⟩
      rw [← hy]; exact hx1.trans hy1
  refine ⟨blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1), blockScalar_central hc0 _, ?_⟩
  intro g hg
  simp only [lowC, Set.mem_ofPred_eq] at hg
  obtain ⟨hK, hlow⟩ := hg
  have hgint : ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hK
    intro i j
    exact (h i j).2
  have h0W : (0 : k) ∈ W := mem_of_mem_nhds hW
  rw [leviEmb_blockScalar]
  refine hVU (hWV _ fun i j => ?_)
  have hentry : (((GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1))⁻¹ * g *
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e i))⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j *
          c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e j) := by
    simp [GlobalTheory.DepthZeroJac.dia, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Matrix.sub_apply, hentry]
  by_cases hij : blk e j < blk e i
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [Matrix.one_apply_ne hne, sub_zero]
    apply hγ
    exact ((valuation_conj_le hc0 hc1 (hgint i j) (GlobalTheory.CompanionTheory.MoyPrasad.expo_gap 1 hij)).trans_eq
      (pow_one _)).trans_lt hcγ
  · have h0 := hlow i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [h0]
    by_cases hij' : i = j
    · subst hij'
      simpa [hc0] using h0W
    · simpa [Matrix.one_apply_ne hij'] using h0W

end GlobalTheory.CompanionTheory.MoyPrasad

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainmentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_open_ideal_containment : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  first | exact @GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image | exact GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image | (intros; apply GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientReductionFirstChernClassTateTwist
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ReductionFirstChern

open GlobalTheory.CompanionTheory.CocCls

section Ring

variable {S S' : Type} [CommRing S] [CommRing S'] {J : Ideal S} {J' : Ideal S'}

theorem dpow_mem_pdP (δ : DividedPowers J) {x : S} (hx : x ∈ J) {k r : ℕ} (h : r ≤ k) : δ.dpow k x ∈ pdP δ r :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simpa using h, by simp⟩

theorem dlog_trunc (δ : DividedPowers J) {s N : ℕ} (hs : pdP δ s = ⊥) (h : s ≤ N) {v : S} (hv : v - 1 ∈ J) :
    B.dlog δ N v = B.dlog δ s v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  have h1 : δ.dpow (k + 1) (v - 1) ∈ pdP δ s := dpow_mem_pdP δ hv (by
    have : s ≤ k := by simpa using hk
    omega)
  rw [hs, Ideal.mem_bot] at h1
  rw [h1, mul_zero]

theorem dlog_red {δ : DividedPowers J} {δ' : DividedPowers J'} {f : S →+* S'} (hf : IsDPMorphism δ δ' f) {s N : ℕ}
    (hs : pdP δ s = ⊥) (hN : ∀ k, N ≤ k → (k.factorial : S') = 0) {v : S} (hv : v - 1 ∈ J) :
    f (B.dlog δ s v) = B.dlog δ' N (f v) := by
  rw [← dlog_trunc δ hs (le_max_left s N) hv, dlog_map hf _ hv]
  exact GlobalTheory.CompanionTheory.FirstChernClassFactorial.dlog_eq_of_factorial δ' (le_max_right s N) hN _

theorem factorial_quot {l : ℕ} (hl : l ≠ 0) (n k : ℕ) (hk : l * n ≤ k) :
    (k.factorial : S ⧸ Ideal.span {(l : S) ^ n}) = 0 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.FirstChernClassFactorial.pow_dvd_factorial_mul l (Nat.pos_of_ne_zero hl) n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : S) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ring

section Lift

variable {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ} {𝒱 : Set X.Opens}
  {C : Type 1} [Category.{0} C] (g : C ⥤ (TS γ q l s 𝒱).FullSubcategory) {D : E.LineData X}

def redLift (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D) :
    B.CLift (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) (g ⋙ redG q s d 𝒱) D where
  p T := Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T
  hp T := by
    rw [Category.assoc, Lf.hp]
    rfl
  w {T T'} φ := Units.map (Ideal.Quotient.mk (lnT (g.obj T').obj l n)).toMonoidHom (Lf.w φ)
  hw {T T'} φ h := by
    have e : B.thSp (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) ((g ⋙ redG q s d 𝒱).map φ) ≫ Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T =
        Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T) := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      unfold B.thSp
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    have h0 := hh Lf φ
    have h2 : (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T)) ≫ D.f =
        (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ Lf.p T') ≫ D.f := by
      rw [Category.assoc, h0, Category.assoc]
    have h3 := uq_map D (qBar (g.obj T').obj l n) _ _ h0 h2
    have h4 := uq_congr D e rfl h h2
    have h5 := Lf.hw φ h0
    change _ = (uq D _ _ h).val
    rw [h4, h3]
    change _ = qBar (g.obj T').obj l n (uq D _ _ h0).val
    refine Eq.trans ?_ (congrArg (qBar (g.obj T').obj l n) h5)
    rfl

theorem r_red (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    (B.CLift.r (redLift d g Lf) σ).val = Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.r Lf σ).val := by
  have h2 : B.CLift.r (redLift d g Lf) σ =
      Units.map (Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n)).toMonoidHom (B.CLift.r Lf σ) := by
    unfold B.CLift.r
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [h2]
  rfl

theorem r_sub (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) : (B.CLift.r Lf σ).val - 1 ∈ (g.obj (σ.obj (Fin.last 2))).obj.J := by
  have hfg : σ.map' 0 2 = σ.map' 0 1 ≫ σ.map' 1 2 := σ.map'_comp 0 1 2
  have h0 : B.CLift.r Lf σ = Rf Lf (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 1 ≫ σ.map' 1 2) := by
    rw [← hfg]
    rfl
  have h1 : red (σ.obj (Fin.last 2)) (g ⋙ (TS γ q l s 𝒱).ι) (B.CLift.r Lf σ) = 1 := by
    rw [h0]
    exact red_Rf Lf _ _
  exact sub_one_mem h1

theorem coc_red {Λ : Type} [CommRing Λ] (c : Λ →+* R)
    (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    B.CLift.coc (redLift d g Lf) c (l * n) σ =
      Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.coc Lf (RingHom.id A) s σ) := by
  have e1 := dlog_red (redδ_dp (g.obj (σ.obj (Fin.last 2))).obj (g.obj (σ.obj (Fin.last 2))).property.1 n) (s := s) (N := l * n)
    (g.obj (σ.obj (Fin.last 2))).property.1.1 (fun k hk => factorial_quot d.hl n k hk) (r_sub g Lf σ)
  exact (congrArg _ (r_red d g Lf σ)).trans e1.symm

end Lift

section Top

variable {b : Base} {L : b.Fun}

theorem idF_ext {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a a' : IdF A}
    (h : a.S = a'.S) : a = a' := by
  cases a
  cases a'
  cases h
  rfl

theorem stdI_top (Q : ObjectProperty (Thick L)) : stdI Q (some 0) 0 = IdF.top _ :=
  idF_ext (funext fun T => top_unique (le_trans (le_of_eq T.obj.pdPow_zero.symm) le_sup_left))

theorem bij_top {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {a e : IdF (sP Q).A} {a' e' : IdF (sP Q').A}
    (ha : a = IdF.top _) (ha' : a' = IdF.top _) (h1 : (incl h).Le a a') (h2 : (incl h).Le e e') (j : ℕ)
    (H : Function.Bijective (((incl h).sq h1 h2).pull j)) :
    Function.Bijective (((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) h2).pull j) := by
  subst ha ha'
  exact H

end Top

theorem coefficientReduction_firstChernClass_tateTwist : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∀ (x : CH.H (B.OM (nlFun δ l X q κ) c) 2) (z : HO (TS γ q l s {⊤}) 2),
    B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) D c (l * n) x → IsFirstChernThickening (TS γ q l s {⊤}) D s z →
    redM (TS γ q l s {⊤}) none ((l : A) ^ n) 2 z = (redMor q s d {⊤} c lam hc none).pull 2 x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s c lam hc D hD x z hx hz
  let Q := TS γ q l s {⊤}
  let Q' := TS γ q l s (𝒱D D)
  have h : Q' ≤ Q := fun T hT => ⟨hT.1, ⊤, rfl, GlobalTheory.CompanionTheory.CrystallineChernClass.inU_top T⟩
  let g : Q'.FullSubcategory ⥤ Q.FullSubcategory := ObjectProperty.ιOfLE h
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hinj := bij_top h (stdI_top Q) (stdI_top Q') _ (incl_std h none ((l : A) ^ n)) 2
    ((GlobalTheory.T.cech_refinement_cohomology_bijective (TF l s) hU (𝒱D D) {⊤} h (by rintro W rfl; rw [hD]) 2).2.1 (some 0) none 0 ((l : A) ^ n))
  obtain ⟨Lf⟩ := GlobalTheory.T.exists_crystalline_lift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ Q.ι) D (fun T =>
    GlobalTheory.CompanionTheory.CrystallineChernClass.st_le_lifts (γ := γ) (p := 0) (q := q) (κ := κA O I) D T.obj ⟨trivial, T.property.2⟩)
  obtain ⟨hz1, hcl1⟩ := hz Q'.FullSubcategory g (fun T => T.property.2) Lf
  let Lr := redLift d g Lf
  obtain ⟨hz2, hcl2⟩ := hx Q'.FullSubcategory (g ⋙ redG q s d {⊤}) Lr
  apply hinj.1
  let P := (incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h none ((l : A) ^ n))
  let M₁ := (toSq (IdF.top _) (stdI Q none ((l : A) ^ n)) fun _ => rfl).comp P
  let M₂ := (redMor q s d {⊤} c lam hc none).comp (σ'' := lam) P
  let m₁ : CH.Mor (g ⋙ CH.modF (sP Q).A) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) (RingHom.id A) :=
    { G := 𝟭 _, τ := fun T => M₁.τ T, nat := fun φ x => M₁.nat φ x }
  let m₂ : CH.Mor ((g ⋙ redG q s d {⊤}) ⋙ B.OM (nlFun δ l X q κ) c) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) lam :=
    { G := 𝟭 _, τ := fun T => M₂.τ T, nat := fun φ x => M₂.nat φ x }
  have hL : P.pull 2 (redM Q none ((l : A) ^ n) 2 z) = m₁.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) g).pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hR : P.pull 2 ((redMor q s d {⊤} c lam hc none).pull 2 x) =
      m₂.pull 2 ((CH.Mor.restrict (B.OM (nlFun δ l X q κ) c) (g ⋙ redG q s d {⊤})).pull 2 x) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hE : m₁.pullC 2 (Lf.coc (RingHom.id A) s) = m₂.pullC 2 (Lr.coc c (l * n)) := by
    funext σ
    have e := coc_red d g c Lf σ
    have t : ∀ (T : Q'.FullSubcategory) (b : (g.obj T).obj.B), m₁.τ T b = m₂.τ T (Ideal.Quotient.mk (lnT (g.obj T).obj l n) b) :=
      fun _ _ => rfl
    exact (t _ _).trans (congrArg (m₂.τ _) e.symm)
  have hb1 : CH.d _ 2 (m₁.pullC 2 (Lf.coc (RingHom.id A) s)) = 0 :=
    (m₁.d_pullC 2 _).trans ((congrArg _ hz1).trans (map_zero _))
  have hb2 : CH.d _ 2 (m₂.pullC 2 (Lr.coc c (l * n))) = 0 :=
    (m₂.d_pullC 2 _).trans ((congrArg _ hz2).trans (map_zero _))
  have a1 := CrystallineSemistableComparison.P.mapH_cls m₁.hom 2 _ hz1 hb1
  have a2 := CrystallineSemistableComparison.P.mapH_cls m₂.hom 2 _ hz2 hb2
  have key : ∀ (w w' : CH.Cn (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) 2) (k : CH.d _ 2 w = 0) (k' : CH.d _ 2 w' = 0),
      w = w' → (CH.cx _).cls w k = (CH.cx _).cls w' k' := by
    rintro _ _ _ _ rfl
    rfl
  exact hL.trans ((congrArg (m₁.pull 2) hcl1.symm).trans (a1.trans ((key _ _ hb1 hb2 hE).trans
    (a2.symm.trans ((congrArg (m₂.pull 2) hcl2).trans hR.symm)))))

end GlobalTheory.CompanionTheory.ReductionFirstChern
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteOfCommuteCyclicMatrixStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_of_commute_cyclic_matrix : ∀ (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) → ∀ X Y : Matrix (Fin n) (Fin n) R, X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X → Y * γ.map (algebraMap K R) = γ.map (algebraMap K R) * Y → X * Y = Y * X := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic | exact GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic | (intros; apply GlobalTheory.CompanionTheory.TorusCh.commute_of_commute_cyclic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficient
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.KType

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finset_sum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem eventually_eq_chart (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a)
    (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, φ.1 (unip x * g) =
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hlev.mem_nhds h1)] with x hx
  have hx' : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) φ = φ := hx
  rw [chart_val, JointCont.unip_mul_eq, ← mul_inv_cancel_left (JointCont.finPart g x₀) (JointCont.finPart g x),
    map_mul, mul_assoc, ← infGL_comm, ← mul_assoc]
  exact congrArg (fun ψ : Sm E a => ψ.1 (finGL E a (JointCont.finPart g x₀) * infGL E a (JointCont.infPart g x))) hx'

theorem continuous_unip_mul (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hf₀ : ContDiffOn ℝ ∞ (chart φ.1 (finGL E a (JointCont.finPart g x₀))) (invSet E a) := φ.2 _
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E =>
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a (JointCont.finPart g x₀)))
      (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  have hE : (fun x : BlockIx a r → Ad E => φ.1 (unip x * g)) =ᶠ[𝓝 x₀]
      fun x => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) :=
    eventually_eq_chart φ hlev g x₀
  exact hA.congr hE.symm

theorem exists_bound_unip_mul (φ : Sm E a) (hleft : ∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hCm : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn (continuous_unip_mul (r := r) φ hlev g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Set.univ.pi fun _ : BlockIx a r => K,
      x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  rw [unip_add, unip_algebraMap, mul_assoc, hleft]
  exact hC x' hx'm

theorem ct_mem_coeffSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  intro E _ _ _ a r φ hleft hlev W _ _ _ ρ hρ _ _ μ 𝓕 hμ hF g
  haveI := hμ
  haveI := finiteDimensional_coeffSpan ρ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine integral_mem (μ.restrict 𝓕) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun x k => φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))) (fun x => ?_) (fun k => ?_)
  · have e : ∀ k : Kinf E a, (cptRep E a k φ).1 (unip x * g) = φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) :=
      fun k => by rw [← mul_assoc]; rfl
    have := hρ (unip x * g)
    simp only [e] at this
    exact this
  · obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) φ hleft hlev (g * infGL E a (Unitary.toUnits k))
    exact Integrable.of_bound (continuous_unip_mul φ hlev _).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)

end GlobalTheory.CompanionTheory.CTFin.KType

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormula
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem constTerm_unip_left : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
    ∀ (y : BlockIx a r → Ad E) (g : GA E a),
      ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ a r φ hl _ _ _ μ 𝓕 hμ h𝓕 y g
  haveI := countable_ratN (E := E) (a := a) r
  have hper : ∀ n ∈ ratN E a r, ∀ x, φ.1 (unip (n + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    rw [unip_add, mul_assoc]
    exact (congrArg (fun u => φ.1 (u * _)) (unip_algebraMap q)).trans (hl _ _)
  have h := Formalism.IndefR.Tow.fd_setIntegral_add h𝓕 (f := fun x => φ.1 (unip x * g)) hper y
  simpa only [unip_add, mul_assoc] using h

end GlobalTheory.CompanionTheory.CTFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnLambdaSubgroupStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_lambda_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (e : Matrix (Fin n) (Fin n) E), e * e = e → (∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ)) → ∀ H : Subgroup (GA E n), (∀ t ∈ H, t.val * rm e = rm e * t.val) → ContinuousOn (lam e) (H : Set (GA E n)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | exact GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam <;> assumption)
end

