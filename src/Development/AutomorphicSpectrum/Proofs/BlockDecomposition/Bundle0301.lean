import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
section
noncomputable section

open NumberField MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def UBnd {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q → ∃ C : ℝ, ∀ i, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) →
      ∀ q ∈ Q, ‖f i (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r)

structure UFam {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  left : ∀ i, IsLeftInvariant (f i)
  level : ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ i (g : AdelicGLn.AdelicGL K n) (u : U),
      f i (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = f i g

abbrev mat (y : archGroup K n) : ArchMatrix K n := ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)

structure Ker [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ) : Prop where
  cont : Continuous β
  cpt : HasCompactSupport β
  nonneg : ∀ y, 0 ≤ β y
  mass : ∫ y, β y ∂ν = 1
  lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ y y', |β y - β y'| ≤ L * ‖mat y - mat y'‖

def sm [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ y, (β y : ℂ) * f (x * infEmb K n y) ∂ν

theorem continuous_mat : Continuous (mat : archGroup K n → ArchMatrix K n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isCompact_ball {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
  have hemb : IsEmbedding (fun y : archGroup K n => mat y) :=
    Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)
  have hsub : Metric.closedBall (1 : ArchMatrix K n) ρ ⊆ Set.range (fun y : archGroup K n => mat y) := by
    intro a ha
    have h1 : ‖1 - a‖ < 1 := by
      rw [norm_sub_rev]
      exact lt_of_le_of_lt (by simpa [dist_eq_norm] using ha) hρ
    refine ⟨⟨Units.oneSub (1 - a) h1, Subgroup.mem_top _⟩, ?_⟩
    simp [mat]
  have := (hemb.isInducing.isCompact_preimage_iff hsub).2 (isCompact_closedBall (1 : ArchMatrix K n) ρ)
  convert this using 1
  ext y
  simp [dist_eq_norm]

theorem tent_lip {A : Type*} [SeminormedAddCommGroup A] {ρ : ℝ} (hρ0 : 0 < ρ) (a b e : A) :
    |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ ρ⁻¹ * ‖a - b‖ := by
  have h1 : |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ |(1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ)| := by
    simp only [max_comm (0 : ℝ)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : (1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ) = ρ⁻¹ * (‖b - e‖ - ‖a - e‖) := by
    field_simp
    ring
  rw [h2, abs_mul, abs_of_pos (inv_pos.2 hρ0)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ0.le))
  have h3 := abs_norm_sub_norm_le (b - e) (a - e)
  rw [sub_sub_sub_cancel_right] at h3
  rw [norm_sub_rev a b]
  exact h3

theorem exists_ker [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {U : Set (archGroup K n)} (hU : U ∈ 𝓝 1) :
    ∃ β, Ker ν β ∧ tsupport β ⊆ U := by
  have hc : ContinuousAt (fun y : archGroup K n => mat y) 1 := continuous_mat.continuousAt

  have hb : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} ⊆ U := by
    have hemb : IsInducing (fun y : archGroup K n => mat y) :=
      (Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)).isInducing
    rw [hemb.nhds_eq_comap, mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    have h1 : mat (1 : archGroup K n) = 1 := rfl
    rw [h1] at ht
    obtain ⟨e, he, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ht
    refine ⟨min e (1 / 2), by positivity, by
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun y hy => hsub ?_⟩
    apply hball
    simp only [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans hy (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hρU⟩ := hb
  set β₀ : archGroup K n → ℝ := fun y => max 0 (1 - ‖mat y - 1‖ / ρ) with hβ₀
  have hβc : Continuous β₀ :=
    continuous_const.max (continuous_const.sub ((continuous_mat.sub continuous_const).norm.div_const _))
  have hsupp : Function.support β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
    intro y hy
    by_contra h
    apply hy
    have h' : ρ < ‖mat y - 1‖ := not_le.1 h
    have : 1 < ‖mat y - 1‖ / ρ := (one_lt_div hρ0).2 h'
    exact max_eq_left (by linarith)
  have hclosed : IsClosed {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} :=
    isClosed_le (continuous_mat.sub continuous_const).norm continuous_const
  have hts : tsupport β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := closure_minimal hsupp hclosed
  have hcs : HasCompactSupport β₀ := (isCompact_ball hρ1).of_isClosed_subset (isClosed_tsupport _) hts
  have hnn : ∀ y, 0 ≤ β₀ y := fun y => le_max_left _ _
  have hpos : 0 < ∫ y, β₀ y ∂ν := by
    refine hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (x := 1) ?_
    have : β₀ 1 = 1 := by simp [hβ₀, mat]
    rw [this]; exact one_ne_zero
  set c := ∫ y, β₀ y ∂ν with hcdef
  have hcpos : 0 ≤ c⁻¹ := inv_nonneg.2 hpos.le
  have hk : Ker ν (fun y => c⁻¹ * β₀ y) := by
    refine { cont := continuous_const.mul hβc
             cpt := hcs.mul_left
             nonneg := fun y => mul_nonneg hcpos (hnn y)
             mass := ?_
             lip := ⟨c⁻¹ * ρ⁻¹, mul_nonneg hcpos (inv_nonneg.2 hρ0.le), fun y y' => ?_⟩ }
    · rw [integral_const_mul, ← hcdef, inv_mul_cancel₀ hpos.ne']
    · rw [← mul_sub, abs_mul, abs_of_nonneg hcpos, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hcpos
      exact tent_lip hρ0 _ _ _
  exact ⟨_, hk, (tsupport_mul_subset_right (f := fun _ => c⁻¹) (g := β₀)).trans (hts.trans hρU)⟩

end GlobalTheory.CompanionTheory.Conc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsAbs
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernComparison

open CrystallineSemistableComparison.CH

universe w w' u v u' v' u'' v''

section Coh
variable {R : Type} [CommRing R] {Th : Type u} [Category.{v} Th] {Ec : Type u'} [Category.{v'} Ec]
  {C : Type u''} [Category.{v''} C]

theorem pull_transport (F : Th ⥤ ModuleCat.{w} R) (F' : Ec ⥤ ModuleCat.{w'} R) (m : Mor F F' (RingHom.id R)) (G : C ⥤ Ec)
    (x : H F 2) (c : Cn ((G ⋙ m.G) ⋙ F) 2) (hc : d _ 2 c = 0)
    (h : (cx _).cls c hc = (Mor.restrict F (G ⋙ m.G)).pull 2 x) :
    ∃ hz : d (G ⋙ F') 2 (fun s => m.τ _ (c s)) = 0,
      (cx _).cls _ hz = (Mor.restrict F' G).pull 2 (m.pull 2 x) := by
  let m' : Mor ((G ⋙ m.G) ⋙ F) (G ⋙ F') (RingHom.id R) :=
    ⟨𝟭 _, fun T => m.τ (G.obj T), fun φ x => m.nat (G.map φ) x⟩
  have hz : d (G ⋙ F') 2 (fun s => m.τ _ (c s)) = 0 := by
    have := m'.d_pullC 2 c
    rw [hc, map_zero] at this
    exact this
  refine ⟨hz, ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 c hc hz
  have e2 : (Mor.restrict F' G).pull 2 (m.pull 2 x) = m'.pull 2 ((Mor.restrict F (G ⋙ m.G)).pull 2 x) := by
    have a := (CrystallineSemistableComparison.P.pull_comp m (Mor.restrict F' G) 2 x).1
    have b := (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F (G ⋙ m.G)) m' 2 x).1
    exact a.symm.trans b
  rw [e2, ← h]
  exact e1.symm

end Coh

section Line
variable {X : Scheme.{0}}

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem u_map (D : E.LineData X) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (a b : Spec (CommRingCat.of A) ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f) (a' b' : Spec (CommRingCat.of B) ⟶ D.Y)
    (ha : a' = Spec.map (CommRingCat.ofHom f) ≫ a) (hb : b' = Spec.map (CommRingCat.ofHom f) ≫ b)
    (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (D.u a' b' h') =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (D.u a b h)) := by
  subst ha hb
  rw [D.nat (Spec.map (CommRingCat.ofHom f)) a b h, ← gamma_nat]
  rfl

theorem u_coc (D : E.LineData X) {U₀ U₁ U₂ : Type} [CommRing U₀] [CommRing U₁] [CommRing U₂]
    (f₁ : U₀ →+* U₁) (f₂ : U₁ →+* U₂) (f₃ : U₀ →+* U₂) (hf : f₃ = f₂.comp f₁)
    (p₀ : Spec (CommRingCat.of U₀) ⟶ D.Y) (p₁ : Spec (CommRingCat.of U₁) ⟶ D.Y) (p₂ : Spec (CommRingCat.of U₂) ⟶ D.Y)
    (h₁ : (Spec.map (CommRingCat.ofHom f₁) ≫ p₀) ≫ D.f = p₁ ≫ D.f)
    (h₂ : (Spec.map (CommRingCat.ofHom f₂) ≫ p₁) ≫ D.f = p₂ ≫ D.f)
    (h₃ : (Spec.map (CommRingCat.ofHom f₃) ≫ p₀) ≫ D.f = p₂ ≫ D.f) :
    f₂ ((Scheme.ΓSpecIso (CommRingCat.of U₁)).hom.hom (D.u _ _ h₁)) *
      (Scheme.ΓSpecIso (CommRingCat.of U₂)).hom.hom (D.u _ _ h₂) =
      (Scheme.ΓSpecIso (CommRingCat.of U₂)).hom.hom (D.u _ _ h₃) := by
  subst hf
  have e : Spec.map (CommRingCat.ofHom (f₂.comp f₁)) = Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h12 : (Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) ≫ p₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom f₂) ≫ p₁) ≫ D.f := by
    simpa only [Category.assoc] using congrArg (Spec.map (CommRingCat.ofHom f₂) ≫ ·) h₁
  have A := u_map D f₂ _ _ h₁ _ _ rfl rfl h12
  have c := D.coc _ _ _ h12 h₂
  have e3 : ∀ (a : Spec (CommRingCat.of U₂) ⟶ D.Y) (ha : a = Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) ≫ p₀)
      (hh : a ≫ D.f = p₂ ≫ D.f), D.u a p₂ hh = D.u _ p₂ (h12.trans h₂) := by
    intro a ha hh; subst ha; rfl
  rw [← A, ← map_mul, ← Units.val_mul, c, e3 _ (by rw [e, Category.assoc]) h₃]

theorem u_square (D : E.LineData X) {U U' Q Q' : Type} [CommRing U] [CommRing U'] [CommRing Q] [CommRing Q']
    (m : U →+* U') (g : U →+* Q) (g' : U' →+* Q') (t : Q →+* Q') (comm : t.comp g = g'.comp m)
    (pT : Spec (CommRingCat.of U) ⟶ D.Y) (pT' : Spec (CommRingCat.of U') ⟶ D.Y)
    (h' : (Spec.map (CommRingCat.ofHom m) ≫ pT) ≫ D.f = pT' ≫ D.f)
    (h : (Spec.map (CommRingCat.ofHom t) ≫ Spec.map (CommRingCat.ofHom g) ≫ pT) ≫ D.f =
      (Spec.map (CommRingCat.ofHom g') ≫ pT') ≫ D.f) :
    (Scheme.ΓSpecIso (CommRingCat.of Q')).hom.hom (D.u _ _ h) =
      g' ((Scheme.ΓSpecIso (CommRingCat.of U')).hom.hom (D.u _ _ h')) := by
  refine u_map D g' _ _ h' _ _ ?_ rfl h
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comm]

end Line

section Log
variable {l : ℕ} [Fact l.Prime]

theorem dxi_mem (k : Bool) (A : PAlg l) (n : ℕ) : A.dxi n 1 ∈ JJ k A n :=
  fil_le k A n (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem dd_dxi (k : Bool) (A : PAlg l) (n m : ℕ) : (DD k A n).dpow m (A.dxi n 1) = A.dxi n m := by
  cases k
  · exact A.dpow_dxi n m
  · have h := (A.dp_fil_pfil n).2 (A.dxi n 1) (Ideal.subset_span ⟨1, le_rfl, rfl⟩) (n := m)
    exact h.trans (A.dpow_dxi n m)

theorem isLog_dlog (k : Bool) (A : PAlg l) (n : ℕ) (u : A.A) (hu : A.sharp u = 1) (v : A.Acr n)
    (hv : v = A.toAcr n (WittVector.teichmuller l u)) :
    E.IsLog A n (WittVector.teichmuller l u) (dlog (DD k A n) (l * n) v) := by
  have h1 : WittVector.teichmuller l u - 1 ∈ Ideal.span {A.xi} := by
    have h0 : A.th (WittVector.teichmuller l u - 1) = 0 := by
      rw [map_sub, map_one]; exact sub_eq_zero.2 hu
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  refine ⟨fun m => algebraMap A.W A.Acr0 c ^ m * A.dxi0 m, fun m => ?_, ?_⟩
  · rw [← hc]
    change algebraMap A.W (Localization.Away (l : A.W)) c ^ m * dpw m A.xi = dpw m (c * A.xi)
    simp only [dpw, map_mul, mul_pow]; ring
  · have hd : v - 1 = A.toAcr n c * A.dxi n 1 := by
      rw [hv, ← toAcr_xi, ← map_mul, hc, map_sub, map_one]
    simp only [dlog, hd]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [DividedPowers.dpow_mul _ (dxi_mem k A n), dd_dxi, map_mul, map_pow]
    rfl

end Log

section Pts
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X}

theorem pt_hom {T T' : C} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (mapU (G.map φ).1.hom)) ≫ (G.obj T).2.1 = (G.obj T').2.1 :=
  congrArg Subtype.val (G.map φ).2

theorem lift_h (Λ : E.Lift G D) {T T' : C} (φ : T ⟶ T') :
    (Spec.map (CommRingCat.ofHom (mapU (G.map φ).1.hom)) ≫ Λ.p T) ≫ D.f = Λ.p T' ≫ D.f := by
  rw [Category.assoc, Λ.hp, Λ.hp]; exact pt_hom φ

theorem mapU_sharp' {A A' : PAlg l} (f : A ⟶ A') (a : A.A) : mapU f (A.sharp a) = A'.sharp (PAlg.Hom.f f a) := by
  change A'.th (mapW f (WittVector.teichmuller l a)) = _
  rw [mapW, WittVector.map_teichmuller]
  rfl

theorem sharp_r (Λ : E.Lift G D) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    (G.obj c₂).1.obj.sharp ((Units.map (PAlg.Hom.f (G.map b).1.hom).toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ :
      ((G.obj c₂).1.obj.A)ˣ) : (G.obj c₂).1.obj.A) = 1 := by
  subst hc
  have wa := Λ.hw a (lift_h Λ a)
  have wb := Λ.hw b (lift_h Λ b)
  have wc := Λ.hw (a ≫ b) (lift_h Λ (a ≫ b))
  have key := u_coc D (mapU (G.map a).1.hom) (mapU (G.map b).1.hom) (mapU (G.map (a ≫ b)).1.hom)
    (by rw [G.map_comp]; exact mapU_comp _ _) (Λ.p c₀) (Λ.p c₁) (Λ.p c₂) (lift_h Λ a) (lift_h Λ b) (lift_h Λ (a ≫ b))
  rw [← wa, ← wb, ← wc, mapU_sharp', ← map_mul] at key
  rw [Units.val_mul, Units.val_mul, map_mul]
  change (G.obj c₂).1.obj.sharp (PAlg.Hom.f (G.map b).1.hom (Λ.w a) * Λ.w b) * _ = 1
  rw [key, ← map_mul, Units.mul_inv, map_one]

end Pts

section Main
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X}

def tm (A : PAlg l) (n : ℕ) : A.A →* A.Acr n :=
  (A.toAcr n).toMonoidHom.comp (WittVector.teichmuller l)

variable (k : Bool) (n : ℕ)

abbrev gG (G : C ⥤ El (PX q κ)) : C ⥤ Thick (Lc (schFn q) κ k n) := G ⋙ gT (schFn q) κ k n

def lam (Λ : E.Lift G D) : CLift (gG k n G) D where
  p T := Spec.map (CommRingCat.ofHom (uJ k (G.obj T).1.obj n)) ≫ Λ.p T
  hp T := by
    rw [Category.assoc, Λ.hp]
    rfl
  w {T T'} φ := Units.map (tm (G.obj T').1.obj n) (Λ.w φ)
  hw {T T'} φ h := by
    have e := u_square D (mapU (G.map φ).1.hom) (uJ k (G.obj T).1.obj n) (uJ k (G.obj T').1.obj n)
      (Ideal.quotientMap _ (mapAcr (G.map φ).1.hom n) (jj_le k (G.map φ).1.hom n)) (uJ_map k (G.map φ).1.hom n)
      (Λ.p T) (Λ.p T') (lift_h Λ φ) h
    refine Eq.trans ?_ e.symm
    rw [← Λ.hw φ (lift_h Λ φ)]
    exact uJ_th k _ n (WittVector.teichmuller l (Λ.w φ).val) |>.symm

theorem units_abs {A₁ A₂ B₁ B₂ : Type} [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂] (t₁ : A₁ →* B₁) (t₂ : A₂ →* B₂)
    (f : A₁ →+* A₂) (g : B₁ →+* B₂) (h : ∀ x, g (t₁ x) = t₂ (f x)) (wa : A₁ˣ) (wb wc : A₂ˣ) :
    Units.map g.toMonoidHom (Units.map t₁ wa) * Units.map t₂ wb * (Units.map t₂ wc)⁻¹ =
      Units.map t₂ (Units.map f.toMonoidHom wa * wb * wc⁻¹) := by
  rw [map_mul, map_mul, map_inv]
  congr 2
  exact Units.ext (h _)

theorem tm_map {A A' : PAlg l} (f : A ⟶ A') (x : A.A) : mapAcr f n (tm A n x) = tm A' n (PAlg.Hom.f f x) := by
  change mapAcr f n (A.toAcr n (WittVector.teichmuller l x)) = A'.toAcr n (WittVector.teichmuller l (PAlg.Hom.f f x))
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem lam_r' (Λ : E.Lift G D) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) :
    Units.map ((gG k n G).map b).φ.toMonoidHom ((lam k n Λ).w a) * (lam k n Λ).w b * ((lam k n Λ).w c)⁻¹ =
      Units.map (tm (G.obj c₂).1.obj n) (Units.map (PAlg.Hom.f (G.map b).1.hom).toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹) :=
  units_abs (tm (G.obj c₁).1.obj n) (tm (G.obj c₂).1.obj n) (PAlg.Hom.f (G.map b).1.hom) (mapAcr (G.map b).1.hom n)
    (tm_map n (G.map b).1.hom) (Λ.w a) (Λ.w b) (Λ.w c)

theorem lam_r (Λ : E.Lift G D) (s : ComposableArrows C 2) :
    ((lam k n Λ).r s).val = (G.obj (s.obj (Fin.last 2))).1.obj.toAcr n (WittVector.teichmuller l (Λ.r s).val) :=
  congrArg Units.val (lam_r' k n Λ (s.map' 0 1) (s.map' 1 2) (s.map' 0 2))

end Main

end GlobalTheory.CompanionTheory.FirstChernComparison
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsPullbackEmptyProductOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaPull

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄

theorem pull_square {R : Type} [CommRing R]
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R}
    {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (m : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₃ (RingHom.id R))
    (b' : CH.Mor F₁ F₄ (RingHom.id R)) (q : CH.Mor F₄ F₃ (RingHom.id R))
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x))
    (n : ℕ) (x : CH.H F₁ n) : b.pull n (m.pull n x) = q.pull n (b'.pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m b n x).1,
    ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b' q n x).1]
  exact CrystallineSemistableComparison.P.prism (m.comp b) (b'.comp q) η hτ n x

theorem pt_nat {P P' : CommRingCat.{0} ⥤ Type} (a : P ⟶ P') {B C : CommRingCat.{0}} (f : B ⟶ C)
    (g : C ⟶ C) (hg : g = 𝟙 C) (y : P.obj B) :
    P'.map g (a.app C (P.map f y)) = P'.map f (a.app B y) := by
  subst hg
  rw [P'.map_id]
  exact ConcreteCategory.congr_hom (a.naturality f) y

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
  (u : Fn.Map F F') (k : Bool) (n : ℕ)

theorem units_pullback_empty_product_one {B B' : Type} [CommRing B] [CommRing B'] (i : B' →+* B) (a : B'ˣ) (ha : a = 1)
    (e : Empty → Bˣ) : (1 : Bˣ) =
      (∏ j, e j) * Units.map (RingHom.id B).toMonoidHom ((1 : Bˣ) ^ 1 * (Units.map i.toMonoidHom a)⁻¹) := by
  subst ha
  simp

def cmpHom (T : El (F.pt κ)) :
    (gT F κ k n ⋙ (pullMorC κ u k n).G).obj T ⟶ ((pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G).obj T where
  φ := RingHom.id _
  u := fun j => j.elim
  comm _ := rfl
  dp := (DPMorphism.id _).isDPMorphism
  hle := fun _ h => h
  pt := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    · exact pt_nat u.u (CommRingCat.ofHom (uJ k T.1.obj n))
        (CommRingCat.ofHom (Ideal.quotientMap _ (RingHom.id _) fun _ h => h))
        (CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))) T.2.1
  hx := fun j => j.elim
  hs := units_pullback_empty_product_one _ _ rfl _
  hv := fun j => j.elim

def cmpNat : gT F κ k n ⋙ (pullMorC κ u k n).G ⟶ (pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G where
  app T := cmpHom κ u k n T
  naturality T T' f := Thick.Hom.ext rfl (funext fun j => j.elim)

theorem beta_pull {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
    (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j) :
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  pull_square (pullMorC κ u k n) (βMor F κ k n) (βMor F' κ k n) (pullMor (u.pt κ) n)
    (cmpNat κ u k n) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.very_ample_union_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  first | exact @GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union | exact GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union | (intros; apply GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union <;> assumption)
end

