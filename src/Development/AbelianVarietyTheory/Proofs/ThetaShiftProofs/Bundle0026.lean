import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LePreimageOfUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecGroup

section General

variable {S : Scheme.{0}} {G T T' : Over S}

theorem left_mul_of_comp [GrpObj G] (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom) {a b : T ⟶ G} {a' b' : T' ⟶ G}
    (ha : a'.left = r ≫ a.left) (hb : b'.left = r ≫ b.left) : (a' * b').left = r ≫ (a * b).left := by
  have e₁ : a' = Over.homMk r hr ≫ a := Over.OverMorphism.ext ha
  have e₂ : b' = Over.homMk r hr ≫ b := Over.OverMorphism.ext hb
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl

theorem left_one [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem map_zero_eq_one {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v') :
    x 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem ext_of_generic {A K : Type} [CommRing A] [Field K] {j : A →+* K} (hj : Function.Injective j)
    [IsSeparated G.hom] {p : Sp A ⟶ S} {a b : Over.mk p ⟶ G} (h : spMap j ≫ a.left = spMap j ≫ b.left) : a = b := by
  have : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have : IsDomain A := hj.isDomain j
  exact Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp A) G.hom ((Over.w a).trans (Over.w b).symm) (spMap j) h)

theorem le_preimage_of_unit {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have h₀ : spMap ρ (⊥ : PrimeSpectrum K) ∈ x ⁻¹ᵁ U := h (x := (⊥ : PrimeSpectrum K)) trivial
  have hs : (show PrimeSpectrum A from p) ⤳ (show PrimeSpectrum A from spMap ρ (⊥ : PrimeSpectrum K)) := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun s hs => ?_
    change ρ s ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    by_contra hne
    exact (show PrimeSpectrum A from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (hρ s hne))
  exact hs.mem_open (x ⁻¹ᵁ U).isOpen h₀

theorem isFrm_map {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (L : LB X) (x : Sp A ⟶ X) (τ : L.ι → A) (h : IsFrm L x τ) :
    IsFrm L (spMap ρ ≫ x) (fun j => ρ (τ j)) := by
  refine ⟨fun j hj => (h.1 j (le_preimage_of_unit ρ hρ x _ hj)).map ρ, fun j j' hj => ?_⟩
  have hx := le_preimage_of_unit ρ hρ x _ hj
  rw [HolHom.valR_spMap ρ x _ hx, ← map_mul, ← h.2 j j' hx]

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y} {Γ : Germs} (Ψ : SpecPts Φ Γ)
  {w : ℂ} (hw : Ψ.T < w.im)

theorem val_base :
    spMap (Γ.R w).val.toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = y := by
  rw [← Category.assoc, spMap_comp_spMap]
  exact Ψ.yT_gen

theorem ev_base :
    spMap (Γ.ev w).toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = Ψ.yw w := by
  rw [← Category.assoc, spMap_comp_spMap, Ψ.yw_eq w hw]
  congr 2
  exact RingHom.ext fun s => Γ.ev_eq Ψ.T w hw s

theorem xt_add (v v' : A.V) : Ψ.xt w hw (v + v') = Ψ.xt w hw v * Ψ.xt w hw v' := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.add]
  exact left_mul_of_comp (T' := Over.mk y) _ (val_base Ψ hw) (Ψ.xt_gen w hw v).symm (Ψ.xt_gen w hw v').symm

theorem xt_act (e : 𝓞 E) (v : A.V) : Ψ.xt w hw (A.actV e v) = Ψ.xt w hw v ≫ t.act.act e := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.lin, Over.comp_left, Over.comp_left, ← Ψ.xt_gen w hw v, Category.assoc]

include hw

theorem pi_add (v v' : A.V) : Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v' := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_add]
  exact (left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (ev_base Ψ hw) (Ψ.pi_eq w hw v) (Ψ.pi_eq w hw v')).symm

theorem pi_act (e : 𝓞 E) (v : A.V) : Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ t.act.act e := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_act, Over.comp_left, Over.comp_left, Ψ.pi_eq w hw, Category.assoc]

theorem pi_frm (v : A.V) : IsFrm t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v) := by
  rw [Ψ.pi_eq w hw]
  exact isFrm_map (Γ.ev w).toRingHom (Γ.unit w) _ _ _ (Ψ.τt_frm w hw v)

theorem pi_rig (j : t.PP.L.ι) (hj : ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ t.PP.L.U j) :
    Ψ.fr w j 0 = valAt' (Ψ.yw w) ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
  rw [Ψ.pi_eq w hw] at hj
  have h₁ : ⊤ ≤ (Ψ.xt w hw 0).left ⁻¹ᵁ t.PP.L.U j := le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ hj
  have h₂ : ⊤ ≤ (Φ.x 0).left ⁻¹ᵁ t.PP.L.U j := by
    rw [← Ψ.xt_gen w hw 0]
    exact fun p _ => h₁ (x := spMap (Γ.R w).val.toRingHom p) trivial
  have h₃ : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ
      (t.PP.L.pull (eSec t.G)).U (fun _ => j) := by
    rw [map_zero_eq_one _ (xt_add Ψ hw), left_one] at h₁
    exact fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  have h₄ : Ψ.τt w 0 j = valR (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)
      ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
    refine Subtype.ext ?_
    rw [Ψ.τt_gen w hw 0 j h₁, Φ.rig j h₂]
    exact (congrArg (fun q => valR q _ _) (val_base Ψ hw).symm).trans
      (HolHom.valR_spMap (Γ.R w).val.toRingHom _ _ h₃ _)
  rw [SpecPts.fr, h₄, HolHom.valAt'_eq_valR, ← ev_base Ψ hw]
  exact (HolHom.valR_spMap (Γ.ev w).toRingHom _ _ h₃ _).symm

omit hw

theorem specPts_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ w : ℂ, Ψ.T < w.im → (∀ v v', Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v') ∧ (∀ (e : 𝓞 E) v, Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ o.t.act.act e) ∧ (∀ v, IsFrm o.t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v)) ∧ ∀ j, ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j 0 = valAt' (Ψ.yw w) ((o.t.PP.L.pull (eSec o.t.G)).U (fun _ => j)) (o.t.PP.rig.s (fun _ => j)).val :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ _ hw =>
    ⟨pi_add Ψ hw, pi_act Ψ hw, pi_frm Ψ hw, pi_rig Ψ hw⟩

end GlobalTheory.SpecGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRealSpanPeriodsOfCharacterKernel
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.PeriodSpan

theorem eq_of_exp_mul_eq {a b : ℂ} (H : ∀ s : ℂ, Complex.exp (s * a) = Complex.exp (s * b)) :
    a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h1 := H (Real.pi * Complex.I / (a - b))
  have h2 : Complex.exp (Real.pi * Complex.I / (a - b) * a - Real.pi * Complex.I / (a - b) * b)
      = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [← mul_sub, div_mul_cancel₀ _ hd, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem exists_block_solution {g : ℕ} (S : Finset (Fin g)) (A : Matrix (Fin g) (Fin g) ℝ)
    (hA : A.PosDef) (y : Fin g → ℝ) :
    ∃ b : Fin g → ℝ, (∀ k ∈ S, b k = 0) ∧ ∀ k ∉ S, A.mulVec b k = y k := by
  classical
  let T : (Fin g → ℝ) →ₗ[ℝ] (Fin g → ℝ) :=
    LinearMap.pi fun k => if k ∈ S then LinearMap.proj k
      else (LinearMap.proj k).comp A.mulVecLin
  have hT : ∀ b k, T b k = if k ∈ S then b k else A.mulVec b k := by
    intro b k
    by_cases hk : k ∈ S <;> simp [T, hk]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    have hpos := hA.dotProduct_mulVec_pos hb0
    have : star b ⬝ᵥ A.mulVec b = 0 := by
      unfold dotProduct
      refine Finset.sum_eq_zero fun k _ => ?_
      have h1 := hT b k
      rw [hb] at h1
      by_cases hk : k ∈ S
      · simp only [hk, if_true, Pi.zero_apply] at h1
        simp [← h1]
      · simp only [hk, if_false, Pi.zero_apply] at h1
        simp [← h1]
    exact hpos.ne' this
  obtain ⟨b, hb⟩ := LinearMap.surjective_of_injective hinj
    (fun k => if k ∈ S then 0 else y k)
  refine ⟨b, fun k hk => ?_, fun k hk => ?_⟩
  · have := hT b k
    rw [hb] at this
    simpa [hk] using this.symm
  · have := hT b k
    rw [hb] at this
    simpa [hk] using this.symm

theorem mem_span_periods : ∀ (g n : ℕ) (S : Finset (Fin g)) (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (ℓ : Fin g → (Fin g → ℂ) →ₗ[ℂ] ℂ), 0 < n → (τ.map Complex.im).PosDef → (∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧ h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) → (∀ k ∈ S, ∀ k' ∈ S, ∀ s : ℂ, Complex.exp (ℓ k (s • p (Pi.single (.inl k') 1))) = eTwoPi (n * s * if k' = k then 1 else 0)) → (∀ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) → ∀ k ∈ S, Complex.exp (ℓ k (p u)) = 1) → ∀ z : Fin g → ℂ, (∀ k ∈ S, ℓ k z = 0) → z ∈ Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u} := by
  classical
  intro g n S h τ p ℓ hn hτ hp hℓ hu z hz
  set R := Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u}
    with hR
  set e : Fin g → Fin g → ℂ := fun k => p (Pi.single (.inl k) 1) with he
  set f : Fin g → Fin g → ℂ := fun k => p (Pi.single (.inr k) 1) with hf
  have hhe : ∀ k, h.mulVec (e k) = Pi.single k 1 := fun k => (hp k).1
  have hhf : ∀ k, h.mulVec (f k) = τ.mulVec (Pi.single k 1) := fun k => (hp k).2
  have hinj : Function.Injective h.mulVec := by
    have hM : h * (Matrix.of fun i k => e k i) = 1 := by
      ext i k
      have := congrFun (hhe k) i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
        using this
    have hM' := mul_eq_one_comm.mp hM
    intro x y hxy
    have := congrArg (Matrix.of fun i k => e k i).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hM'] using this
  have hℓe : ∀ k ∈ S, ∀ k' ∈ S, ℓ k (e k') =
      2 * Real.pi * Complex.I * n * if k' = k then 1 else 0 := by
    intro k hk k' hk'
    refine eq_of_exp_mul_eq fun s => ?_
    have := hℓ k hk k' hk' s
    rw [map_smul, smul_eq_mul, eTwoPi] at this
    rw [he]
    refine this.trans ?_
    congr 1
    ring
  have hre : ∀ r ∈ R, ∀ k ∈ S, (ℓ k r).re = 0 := by
    intro r hr k hk
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu', rfl⟩ := hx
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (hu u hu' k hk)
      rw [hm]
      simp
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx =>
      rw [← Complex.coe_smul, map_smul]
      simp [hx]
  have heR : ∀ k, e k ∈ R := fun k =>
    Submodule.subset_span ⟨Pi.single (.inl k) 1, fun k' _ => by simp, rfl⟩
  have hfR : ∀ k ∉ S, f k ∈ R := fun k hk =>
    Submodule.subset_span ⟨Pi.single (.inr k) 1, fun k' hk' => by
      have : k' ≠ k := fun e => hk (e ▸ hk')
      simp [this], rfl⟩
  obtain ⟨b, hbS, hb⟩ := exists_block_solution S _ hτ fun k => (h.mulVec z k).im
  set c : Fin g → ℂ := h.mulVec z - τ.mulVec fun k => (b k : ℂ) with hc
  have hcim : ∀ k ∉ S, (c k).im = 0 := by
    intro k hk
    have := hb k hk
    simp only [hc, Pi.sub_apply, Complex.sub_im]
    rw [← this]
    simp [Matrix.mulVec, dotProduct]
  have hzeq : z = ∑ k, (b k : ℂ) • f k + ∑ k, c k • e k := by
    apply hinj
    have h1 : ∑ k, (b k : ℂ) • (Pi.single k 1 : Fin g → ℂ) = fun k => (b k : ℂ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : ∑ k, c k • (Pi.single k 1 : Fin g → ℂ) = c := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hhe, hhf, h2]
    simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum, h1]
    rw [hc]; abel
  set r : Fin g → ℂ := ∑ k, (b k : ℂ) • f k + ∑ k, ((c k).re : ℂ) • e k with hr
  have hrR : r ∈ R := by
    refine R.add_mem (R.sum_mem fun k _ => ?_) (R.sum_mem fun k _ => ?_)
    · by_cases hk : k ∈ S
      · simp [hbS k hk]
      · rw [Complex.coe_smul]; exact R.smul_mem _ (hfR k hk)
    · rw [Complex.coe_smul]; exact R.smul_mem _ (heR k)
  have hzr : z = r + ∑ k, (((c k).im : ℂ) * Complex.I) • e k := by
    rw [hr, add_assoc, ← Finset.sum_add_distrib]
    simp only [← add_smul, Complex.re_add_im]
    exact hzeq
  have him : ∀ k, (c k).im = 0 := by
    intro k
    by_cases hk : k ∈ S
    · have h0 := hz k hk
      rw [hzr, map_add, map_sum, Finset.sum_eq_single k] at h0
      · have h1 := congrArg Complex.re h0
        rw [map_smul, hℓe k hk k hk, Complex.add_re, hre r hrR k hk] at h1
        simpa [Real.pi_ne_zero, hn.ne'] using h1
      · intro k' _ hne
        by_cases hk' : k' ∈ S
        · rw [map_smul, hℓe k hk k' hk']
          simp [hne]
        · simp [hcim k' hk']
      · simp
    · exact hcim k hk
  rw [hzr]
  simpa [him] using hrR

end GlobalTheory.PeriodSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ArcThetaSpaces

open TwistedTheta

section

variable {P : Out.PolAV (Sp ℂ)} {g : ℕ} {u : HolUnif P.A P.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem eq_zero_of_val (u : HolUnif P.A P.L g) (U : P.A.left.Opens) (f : Γ(P.A.left, U))
    (h : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U f = 0) : f = 0 := by
  have := P.isAb.smooth
  have := isReduced_of_smooth_complex _ P.A.hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq P.A.hom _ _ _ fun x hx hi => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
  rw [h z hi, valAt'_zero]

theorem finite_thetaShift (hT : Out.GlobalSectionsRankAlgClosed) {j : ℕ} (hj : 1 ≤ j)
    (h₁ : ∀ s, ∃ θ, u.IsFnPow j s θ) (h₂ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ) (c : Fin g → ℂ) :
    Module.Finite ℂ (thetaShift u Hm χ j c) := by
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℂ, c = j • b := ⟨(j : ℂ)⁻¹ • c, by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (by omega))]⟩
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P j hj
  choose φ hφ using h₁
  have hle : thetaShift u Hm χ j (j • b) ≤ Submodule.span ℂ (Set.range fun i z => φ (β i) (z + b)) := by
    intro θ hθ
    obtain ⟨s, hs⟩ := h₂ _ (isThetaFn_sub hθ)
    obtain ⟨a, ha, -⟩ := hβ s
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨a, funext fun z => ?_⟩
    have hi := FrameValue.le_chartAt P.isLB (u.ex (z + b)).left
    set i := FrameValue.chartAt P.isLB (u.ex (z + b)).left
    have hi' : ⊤ ≤ (u.ex (z + b)).left ⁻¹ᵁ (lbPow P.L j).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := (valAt'_sum _ _ _ _).symm.trans
      ((congrArg (valAt' _ _) (ha fun _ => i)).symm.trans (hs (fun _ => i) (z + b) hi'))
    simp only [add_sub_cancel_right] at e
    refine mul_right_cancel₀ (pow_ne_zero j (u.fr_ne i _ hi)) (Eq.trans ?_ e)
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Eq.trans ?_ ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      (valAt'_constFn _ _ (Over.w (u.ex (z + b))) _ _ hi') (hφ _ _ _ hi'))).symm
    simp [_root_.mul_assoc]
  have := Module.Finite.span_of_finite ℂ (Set.finite_range fun i z => φ (β i) (z + b))
  exact Submodule.finiteDimensional_of_le hle

theorem mem_thetaShift_zero {j : ℕ} {θ : (Fin g → ℂ) → ℂ} (h : u.IsThetaFn Hm χ j θ) : θ ∈ thetaShift u Hm χ j 0 :=
  ⟨h.1, fun l z => by rw [h.2 l z, FrameValue.hermForm_zero_left]; simp⟩

theorem exists_ne_zero (hT : Out.GlobalSectionsRankAlgClosed) (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  obtain ⟨β, hβ⟩ := PowSec.exists_indep_sections hT P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  by_contra hne
  push_neg at hne
  have h0 : ∀ i j, (β i).f j = 0 := fun i j => eq_zero_of_val u _ _ fun z hz => by
    obtain ⟨θ, h, h'⟩ := h₁ (β i)
    rw [h' j z hz, hne θ h, Pi.zero_apply, zero_mul]
  exact one_ne_zero (congrFun (hβ 1 fun j => by simp [h0]) i₀)

theorem exists_isFn (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) (th : P.L.Sec) (h : ∃ j, th.f j ≠ 0) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 ∧ u.IsFn th θ := by
  obtain ⟨θ, h₂, h₃⟩ := h₁ (secToPow th 1)
  have hf : u.IsFn th θ := fun i z hi => by
    have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := h₃ (fun _ => i) z hi'
    rw [pow_one] at e
    refine Eq.trans ?_ e
    exact ((valAt'_res _ _ (th.f i ^ 1) hi').trans (by rw [pow_one])).symm
  refine ⟨θ, h₂, ?_, hf⟩
  rintro rfl
  obtain ⟨j, hj⟩ := h
  exact hj (eq_zero_of_val u _ _ fun z hz => by rw [hf j z hz, Pi.zero_apply, zero_mul])

end

theorem sections_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ (j : ℕ) (α : Λ.A.X), 1 ≤ j → (∀ s, Λ.fn j α s ∈ Λ.A.Theta j α) ∧ ∀ th ∈ Λ.A.Theta j α, ∃! s, Λ.fn j α s = th) ∧ AnFin Λ.A ∧ ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∃ θ ∈ Λ.A.Theta 1 0, θ ≠ 0 ∧ Λ.u.IsFn th θ := by
  intro hL _ E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hT := theta_eq_thetaShift Λ.A Λ.u (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) Λ.lam
    (fun l l' e => congrArg Λ.A.chi (Subtype.ext e))
  have h0 : Λ.A.ct 0 = 0 := map_zero _
  have hθ : ∀ n θ, Λ.u.IsThetaFn Λ.A.Hm (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) n θ → ∃ s, Λ.u.IsFnPow n s θ :=
    fun n θ h => ((Λ.pow n).2 θ h).exists
  refine ⟨fun j α hj => ?_, ⟨fun j α hj => ?_, ?_⟩, fun th h => ?_⟩
  · rw [hT]
    refine ⟨fun s => secFn_mem Λ.ah (Λ.ct α) s, fun th hth => ?_⟩
    obtain ⟨s, hs⟩ := exists_secFn_eq Λ.ah (by omega) (hθ j) (Λ.ct α) hth
    exact ⟨s, hs, fun t ht => secFn_injective (Λ.ct α) (ht.trans hs.symm)⟩
  · rw [hT]
    exact finite_thetaShift hL.globalSectionsRank hj (fun s => ((Λ.pow j).1 s).exists.imp fun _ h => h.2) (hθ j) _
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_ne_zero hL.globalSectionsRank fun s => ((Λ.pow 1).1 s).exists
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_isFn (fun s => ((Λ.pow 1).1 s).exists) th h
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩

end GlobalTheory.ArcThetaSpaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecValue

variable {K R : Type} [CommRing K] [CommRing R] {X Z : Scheme.{0}}

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  exact congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

def subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := s.f j - ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    rw [map_sub, map_sub, map_sum, map_sum, mul_sub, s.compat j k, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_subComb (p : X ⟶ Sp K) {M : LB X} (s : M.Sec) {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec)
    (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((subComb p s r σ).f j) = valR q _ (s.f j) - ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, subComb, map_sub, map_sum, map_mul]

theorem sval_subComb {L : LB Z} {π : X ⟶ Z} {m : ℕ} (p : X ⟶ Sp K) (s : SecP L π m) {n : ℕ} (r : Fin n → K)
    (σ : Fin n → SecP L π m) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : L.ι)
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (subComb p s r σ : SecP L π m) q j = ArcPts.sval s q j - ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  have hw : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => h hz
  exact valR_subComb p s r σ f q hq (fun _ => j) hw

theorem sval_eq_zero {L : LB Z} {π : X ⟶ Z} {m : ℕ} (s : SecP L π m) (hs : ∀ i, s.f i = 0) (q : Sp R ⟶ X) (j : L.ι) :
    ArcPts.sval s q j = 0 := by
  refine (congrArg (valR q _) (hs fun _ => j)).trans ?_
  by_cases h : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j)
  · exact (HolHom.valR_eq q _ h 0).trans (map_zero _)
  · exact dif_neg h

end SecValue

theorem sval_eq_sum_of_hasVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (j : ℕ) [NeZero j] (s : SecP t.PP.L (pullback.fst t.G.hom y) j) (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ), (∀ i, th i ∈ A.Theta j (α i)) → (∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (∑ i, r i * A.FSum j (α i) (th i) v)) → ∀ (R : Type) [CommRing R] (f : ℂ⸨X⸩ →+* R) (q : Sp R ⟶ pullback t.G.hom y), q ≫ pullback.snd _ _ = spMap f → ∀ jj, ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U jj → sval s q jj = ∑ i, f (r i) * sval (Φ.sig j (α i) (th i)) q jj := by
  intro E _ _ _ H _ S A t y Φ j _ s n r α th hth hs R _ f q hq jj hjj
  have h0 := Φ.sep j (SecValue.subComb (pullback.snd t.G.hom y) s r fun i => Φ.sig j (α i) (th i)) fun v k hk => by
    have hv : fib (Φ.x v) ≫ pullback.snd t.G.hom y = spMap (RingHom.id _) := by
      rw [fib, pullback.lift_snd]
      exact (Spec.map_id _).symm
    rw [SecValue.sval_subComb _ s r _ _ _ hv k hk, hs v k hk, Finset.sum_mul, zero_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Φ.val j (α i) (th i) (hth i) v k hk, RingHom.id_apply, _root_.mul_assoc]
  have h1 := SecValue.sval_eq_zero _ h0 q jj
  rwa [SecValue.sval_subComb _ s r _ f q hq jj hjj, sub_eq_zero] at h1

end GlobalTheory.ArcPts
end
end

