import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.Corev.UnrPow

theorem exists_pow_unrAt : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  intro L _ _ χ
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := GlobalTheory.Mem.FinOrder.exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    exact hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu m) (hx x hu)
  choose m hm0 hm using hm
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun v x hx => ?_⟩
  show χ.loc v x ^ (∏ v ∈ hfin.toFinset, m v) = 1
  by_cases hv : χ.UnrAt v
  · rw [hv x hx, one_pow]
  · obtain ⟨d, hd⟩ : m v ∣ ∏ v ∈ hfin.toFinset, m v := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
    rw [hd, pow_mul, hm v x hx, one_pow]

end GlobalTheory.Corev.UnrPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.VolBridge

variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} (e : A ≃ Fin N)

def locHom : (Sp E N ≃ₗ[E] Sp E N) →* GL A k where
  toFun x := ⟨toLoc ι e e x.toLinearMap, toLoc ι e e (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap,
    by
      rw [← toLoc_comp_square]
      have h : x.toLinearMap ∘ₗ (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square],
    by
      rw [← toLoc_comp_square]
      have h : (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap ∘ₗ x.toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square]⟩
  map_one' := by
    ext1
    show toLoc ι e e (LinearEquiv.refl E (Sp E N)).toLinearMap = 1
    exact toLoc_id_square ι e
  map_mul' x y := by
    ext1
    show toLoc ι e e (x * y).toLinearMap = toLoc ι e e x.toLinearMap * toLoc ι e e y.toLinearMap
    rw [← toLoc_comp_square]
    rfl

theorem locHom_val (x : Sp E N ≃ₗ[E] Sp E N) : (locHom ι e x).val = toLoc ι e e x.toLinearMap := rfl

section Num
variable {A : Type} {N c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (N + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = N + i.val)

include hcc he in
theorem eX_lt (a : A) : (e (Sum.inl a)).val < N := by
  by_contra h
  push Not at h
  have hc : (e (Sum.inl a)).val - N < c := by have := (e (Sum.inl a)).isLt; omega
  have h2 : e (Sum.inr ⟨_, hc⟩) = e (Sum.inl a) := Fin.ext (by rw [he]; simp; omega)
  exact absurd (e.injective h2) (by simp)

def eX : A ≃ Fin N :=
  Equiv.ofBijective (fun a => ⟨(e (Sum.inl a)).val, eX_lt e hcc he a⟩) (by
    constructor
    · intro a b hab
      have : e (Sum.inl a) = e (Sum.inl b) := Fin.ext (by simpa using congrArg Fin.val hab)
      simpa using e.injective this
    · intro m
      rcases hm : e.symm (Fin.castAdd c' m) with a | i
      · refine ⟨a, Fin.ext ?_⟩
        have := congrArg (fun z => (e z).val) hm
        simp at this
        simp [← this]
      · exfalso
        have := congrArg (fun z => (e z).val) hm
        simp [he] at this
        have := m.isLt
        omega)

theorem eX_val (a : A) : ((eX e hcc he a : Fin N) : ℕ) = (e (Sum.inl a)).val := rfl

end Num

section Ext
variable {E : Type} [Field E] {N c : ℕ}

def extX (c : ℕ) (y : Sp E N ≃ₗ[E] Sp E N) : Sp E (N + c) ≃ₗ[E] Sp E (N + c) :=
  (LinearEquiv.funCongrLeft E E finSumFinEquiv) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E) ≪≫ₗ
    (y.prodCongr (LinearEquiv.refl E (Fin c → E))) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E).symm ≪≫ₗ
    (LinearEquiv.funCongrLeft E E finSumFinEquiv).symm

theorem extX_castAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin N) :
    extX c y v (Fin.castAdd c i) = y (fun i => v (Fin.castAdd c i)) i := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]
  rfl

theorem extX_natAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin c) :
    extX c y v (Fin.natAdd N i) = v (Fin.natAdd N i) := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]

end Ext

end GlobalTheory.VolBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocalStatement
section
open NumberField IsDedekindDomain Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_cocycle_integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  first | exact @GlobalTheory.CocIntLoc.integral_of_local | exact GlobalTheory.CocIntLoc.integral_of_local | (intros; apply GlobalTheory.CocIntLoc.integral_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem mem_KO_iff_intAt_isUnit_det : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  let e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
    (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = zPos a := by
    rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring
  let A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E := Matrix.of fun s s' => M s.1 s'.1
  let T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b))
  have hT : T = (A.map ι).submatrix e e := by
    ext a b; simp [T, A, he]
  have hdet : T.det = ι A.det := by
    rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (h3 _ ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k] :=
      Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (h3 _ hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.SymBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditions
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatResidue

theorem zPos_lt {κ τ l j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rcases a with (i | i) | ⟨s, u⟩
  · have := i.isLt
    simp only [zPos]
    omega
  · have := i.isLt
    simp only [zPos]
    omega
  · have hs := s.isLt
    have hu := u.isLt
    have h2 : ((s : ℕ) + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ hs
    rw [Nat.add_mul, one_mul] at h2
    simp only [zPos]
    omega

theorem zPos_injective {κ τ l j : ℕ} {a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j} (h : zPos a = zPos b) : a = b := by
  rcases a with (i | i) | ⟨s, u⟩ <;> rcases b with (i' | i') | ⟨s', u'⟩ <;> simp only [zPos] at h
  · obtain rfl := Fin.ext h
    rfl
  · have := i.isLt
    omega
  · have := i.isLt
    omega
  · have := i'.isLt
    omega
  · obtain rfl := Fin.ext (Nat.add_left_cancel h)
    rfl
  · have := i.isLt
    omega
  · have := i'.isLt
    omega
  · have := i'.isLt
    omega
  · have e1 := PatPlaces.block_div (r := κ + l) (i := (s : ℕ)) u.isLt
    have e2 := PatPlaces.block_div (r := κ + l) (i := (s' : ℕ)) u'.isLt
    rw [h, e2] at e1
    obtain rfl : s = s' := Fin.ext e1.symm
    obtain rfl : u = u' := Fin.ext (Nat.add_left_cancel h)
    rfl

theorem places_to_pattern (F : Type) [Zero F] [One F] (κ ρ l τ j : ℕ) (R : ℕ → ℕ → F) :
    ((∀ p', p' < κ + l → R p' p' = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' →
        (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ →
        (p' - (κ + l)) / τ < (p - (κ + l)) / τ → R p p' = 0)) →
    (∀ (a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  rintro ⟨hA, hB⟩ a b hab
  by_cases he : a = b
  · subst he
    rw [if_pos rfl]
    rcases a with (i | i) | ⟨s, u⟩
    · exact (hA _ (by have := i.isLt; simp only [zPos]; omega)).1
    · exact (hA _ (by have := i.isLt; simp only [zPos]; omega)).1
    · exact absurd (by simp [FreeIx]) hab
  · rw [if_neg he]
    have hne : zPos a ≠ zPos b := fun h => he (zPos_injective h)
    have hs1 := PatPlaces.symIdx_cases κ ρ (zPos a)
    have hs2 := PatPlaces.symIdx_cases κ ρ (zPos b)
    rcases b with (j' | j') | ⟨s', u'⟩
    · refine (hA _ (by have := j'.isLt; simp only [zPos]; omega)).2 _ (zPos_lt a) hne ?_
      rcases a with (i | i) | ⟨s, u⟩
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · left
        simp only [zPos]
        omega
    · refine (hA _ (by have := j'.isLt; simp only [zPos]; omega)).2 _ (zPos_lt a) hne ?_
      rcases a with (i | i) | ⟨s, u⟩
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · left
        simp only [zPos]
        omega
    · rcases a with (i | i) | ⟨s, u⟩
      · exact absurd (by simp [FreeIx]) hab
      · exact absurd (by simp [FreeIx]) hab
      · have hlt : (s' : ℕ) < s := by
          simp only [FreeIx, not_le, Fin.lt_iff_val_lt_val] at hab
          exact hab
        refine hB _ _ (by simp only [zPos]; omega) (zPos_lt _) (zPos_lt _) ?_
        simp only [zPos]
        rw [PatPlaces.block_div u'.isLt, PatPlaces.block_div u.isLt]
        exact hlt

theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ l τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + l → R p' p' = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' →
        (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ →
        (p' - (κ + l)) / τ < (p - (κ + l)) / τ → R p p' = 0)) := by
  intro hpat
  refine ⟨fun p' hp' => ?_, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨a, rfl⟩ := PatPlaces.zPos_surj (show p' < κ + l + j * τ by omega)
    refine ⟨?_, fun p hp hne hcond => ?_⟩
    · have h0 := hpat a a (by
        rcases a with (i | i) | ⟨s, u⟩
        · simp [FreeIx, FreeTop]
        · simp [FreeIx, FreeTop]
        · simp only [zPos] at hp'
          omega)
      rwa [if_pos rfl] at h0
    · obtain ⟨c, rfl⟩ := PatPlaces.zPos_surj hp
      have hca : c ≠ a := fun h => hne (h ▸ rfl)
      rw [hpat c a ?_, if_neg hca]
      have hs1 := PatPlaces.symIdx_cases κ ρ (zPos c)
      have hs2 := PatPlaces.symIdx_cases κ ρ (zPos a)
      rcases a with (i | i) | ⟨s', u'⟩
      · rcases c with (i' | i') | ⟨s, u⟩
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · simp [FreeIx]
      · rcases c with (i' | i') | ⟨s, u⟩
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · simp [FreeIx]
      · simp only [zPos] at hp'
        omega
  · obtain ⟨a, rfl⟩ := PatPlaces.zPos_surj h2
    obtain ⟨c, rfl⟩ := PatPlaces.zPos_surj h3
    rcases a with (i | i) | ⟨s', u'⟩
    · have := i.isLt
      simp only [zPos] at h1
      omega
    · have := i.isLt
      simp only [zPos] at h1
      omega
    · rcases c with (i | i) | ⟨s, u⟩
      · have h0 : zPos (Sum.inl (Sum.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) - (κ + l) = 0 := by
          have := i.isLt
          simp only [zPos]
          omega
        rw [h0, Nat.zero_div] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · have h0 : zPos (Sum.inl (Sum.inr i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) - (κ + l) = 0 := by
          have := i.isLt
          simp only [zPos]
          omega
        rw [h0, Nat.zero_div] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · simp only [zPos] at h4
        rw [PatPlaces.block_div u'.isLt, PatPlaces.block_div u.isLt] at h4
        rw [hpat _ _ ?_, if_neg ?_]
        · intro h
          cases h
          exact lt_irrefl _ h4
        · simp only [FreeIx, Fin.le_iff_val_le_val]
          omega

section Entry
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem entry_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {m : E} (hm : IntAt P m) (c : Prop) [Decidable c] :
    valuation k (ι m - (if c then 1 else 0)) < 1 ↔ redP P m = if c then 1 else 0 := by
  have hI := (GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU).2.1
  by_cases hc : c
  · simp only [if_pos hc]
    have h0 : ι m - 1 = ι (m + algebraMap (𝓞 E) E (-1)) := by
      simp [sub_eq_add_neg]
    rw [h0, hI _ (hm.add (IntAt.coe P _)), reduction_add hm (IntAt.coe P _), reduction_coe]
    simp [add_neg_eq_zero]
  · simp only [if_neg hc, sub_zero]
    exact hI m hm

end Entry

theorem pattern_iff_places : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l ρ τ j : ℕ) (M : ℕ → ℕ → E), (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) → ((∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔ ((∀ p', p' < κ + l → redP P (M p' p') = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' → (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → redP P (M p p') = 0) ∧ (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ → (p' - (κ + l)) / τ < (p - (κ + l)) / τ → redP P (M p p') = 0))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l ρ τ j M hM
  have h : (∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b →
      valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔
      (∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → redP P (M (zPos a) (zPos b)) = if a = b then 1 else 0) := by
    refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_
    rw [Matrix.one_apply]
    exact entry_iff hC hU (hM _ _ (zPos_lt a) (zPos_lt b)) (a = b)
  rw [h]
  exact ⟨pattern_to_places _ κ ρ l τ j fun p p' => redP P (M p p'),
    places_to_pattern _ κ ρ l τ j fun p p' => redP P (M p p')⟩

end GlobalTheory.PatResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRowStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symLevelChain_testFunction_add_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ s', x (Sum.inr q) (Sum.inl s') = 0) → ∀ v : XIx (Fin κ) t j → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0) = if ∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.RowShift.phi_add_row | exact GlobalTheory.SymChain.RowShift.phi_add_row | (intros; apply GlobalTheory.SymChain.RowShift.phi_add_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPoint
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem GlobalTheory.symLevel_lam_residue_elim : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  exact GlobalTheory.symLevel_lam_residue E K k P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
end

