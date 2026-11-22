import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrimePowerNotDvdDifferentStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_power_not_dvd_different : ∀ (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime] (p k : ℕ), p.Prime → (p : 𝓞 E) ∈ P → ¬ P ∣ J → Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J → ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | exact GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | (intros; apply GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RealMpData
section
noncomputable section

open MeasureTheory Complex Matrix
open scoped Real SchwartzMap ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open GlobalTheory.RealWeil

variable {l : Type} [Fintype l] [DecidableEq l]

def RealMpData {G : Type} [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (omS : G →* (Sch l →L[ℂ] Sch l)) : Prop :=
  (IsCoveringMap pr ∧ Function.Surjective pr ∧
    ∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧
  (∀ f : L2 l, Continuous fun g => om g f) ∧
  (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
    om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧
  (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧
  (∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
    (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
    ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2)) ∧
  (∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
    ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0)

def FlowOf {G : Type} [Group G] [TopologicalSpace G] (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (γ : ℝ → G) : Prop :=
  Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0

omit [DecidableEq l] in

def gaussFun (Z : Matrix l l ℂ) (x : EuclideanSpace ℝ l) : ℂ :=
  cexp (-(π : ℂ) * ∑ j, ∑ k, Z j k * (x j : ℂ) * (x k : ℂ))

omit [DecidableEq l] in

def GaussAdm (Z : Matrix l l ℂ) : Prop := Zᵀ = Z ∧ (Z.map Complex.re).PosDef

omit [Fintype l] [DecidableEq l] in

def realify (Z : Matrix l l ℂ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  fromBlocks (Z.map Complex.re) (-(Z.map Complex.im)) (Z.map Complex.im) (Z.map Complex.re)

omit [Fintype l] [DecidableEq l] in

def dilX (S : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks S 0 0 (-S)

omit [Fintype l] [DecidableEq l] in

def chirpX (C : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks 0 0 C 0

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocal
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.ResKCoords

theorem map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  ext x
  rw [← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff e.symm x

theorem rsp_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by
  refine ⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]
  exact (Ideal.map_span e (Set.range r)).symm

theorem stalk_to_localization : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) →
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
      (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
    ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro Y U y hy hreg m f hr
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨y, hy⟩
  let e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv
  have he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a := fun a =>
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩
  · have h := rsp_of_ringEquiv e m _ hr
    simpa only [he] using h
  · rw [Scheme.mem_basicOpen Y s y hy]
    have h := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s
    exact h.trans Iff.rfl

end GlobalTheory.CompanionTheory.ResKCoords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RelIndexBoxLatticesProduct
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex

open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV

section Line

variable {F : Type} [Field F]

def line (O : Subring F) (c : F) : AddSubgroup F :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft c)

theorem mem_line {O : Subring F} {c x : F} : x ∈ line O c ↔ ∃ o ∈ O, x = c * o := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩

theorem map_line (O : Subring F) (e c : F) :
    (line O c).map (AddMonoidHom.mulLeft e) = line O (e * c) := by
  ext x
  simp only [AddSubgroup.mem_map, mem_line, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    exact ⟨o, ho, by ring⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨c * o, ⟨o, ho, rfl⟩, by ring⟩

end Line

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem line_le_of_val_le (h : LF O ϖ nrm q) {x y : F} (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : line O x ≤ line O y := by
  have hvy : 0 < ValuativeRel.valuation F y := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy)
  have h1 : x / y ∈ O := by
    rw [mem_iff_val_le h, map_div₀]
    exact div_le_one_of_le₀ hxy zero_le'
  intro z hz
  obtain ⟨o, ho, rfl⟩ := mem_line.1 hz
  exact mem_line.2 ⟨x / y * o, O.mul_mem h1 ho, by field_simp⟩

theorem line_eq_of_val_eq (h : LF O ϖ nrm q) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x = ValuativeRel.valuation F y) : line O x = line O y :=
  le_antisymm (line_le_of_val_le h hy hxy.le) (line_le_of_val_le h hx hxy.ge)

theorem ball_eq_line (h : LF O ϖ nrm q) {d : F} (hd : d ≠ 0) : ball d = line O d⁻¹ := by
  ext x
  rw [mem_ball, mem_line, ← h.O_eq]
  constructor
  · intro hx
    exact ⟨_, hx, by field_simp⟩
  · rintro ⟨o, ho, rfl⟩
    rwa [mul_comm d⁻¹, mul_assoc, inv_mul_cancel₀ hd, mul_one]

theorem relIndex_line_pow (h : LF O ϖ nrm q) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (line O (c * ϖ ^ k)).relIndex (line O c) = q ^ k := by
  have hϖ0 : ϖ ^ k ≠ 0 := pow_ne_zero _ h.ne
  have hp : ∃ p : 𝒪[F], Irreducible p ∧ (p : F) = (Units.mk0 ϖ h.ne : Fˣ) :=
    ⟨_, irreducible_pi h, rfl⟩
  have h1 := relIndex_ball (Units.mk0 ϖ h.ne) hp (k : ℤ)
  have hu : (((Units.mk0 ϖ h.ne : Fˣ) ^ (k : ℤ) : Fˣ) : F) = ϖ ^ k := by simp
  rw [hu, ball_eq_line h one_ne_zero, ball_eq_line h hϖ0, Int.toNat_natCast, inv_one] at h1
  have hinj : Function.Injective (AddMonoidHom.mulLeft (c * ϖ ^ k)) :=
    mul_right_injective₀ (mul_ne_zero hc hϖ0)
  have h2 := AddSubgroup.relIndex_map_map_of_injective (line O 1) (line O (ϖ ^ k)⁻¹) hinj
  rw [map_line, map_line, mul_one, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one] at h2
  rw [h2, h1, h.card]
  rfl

theorem relIndex_line (h : LF O ϖ nrm q) {c o : F} (hc : c ≠ 0) (ho : o ∈ O) (ho0 : o ≠ 0) :
    (((line O (c * o)).relIndex (line O c) : ℕ) : ℝ) = nrm c / nrm (c * o) := by
  obtain ⟨k, hk⟩ := val_eq_pow_of_int h ho0 ((mem_iff_val_le h o).1 ho)
  have hline : line O (c * o) = line O (c * ϖ ^ k) :=
    line_eq_of_val_eq h (mul_ne_zero hc ho0) (mul_ne_zero hc (pow_ne_zero _ h.ne))
      (by rw [map_mul, map_mul, hk, map_pow])
  have hq : (q : ℝ) ≠ 0 := by
    have := one_lt_q h
    exact_mod_cast (by omega : q ≠ 0)
  have hn : nrm o = ((q : ℝ) ^ k)⁻¹ := by
    have := nrm_eq_zpow h (x := o) (e := (k : ℤ)) (by simpa using hk)
    simpa [_root_.zpow_neg] using this
  have hnc : nrm c ≠ 0 := (nrm.pos hc).ne'
  rw [hline, relIndex_line_pow h hc k, map_mul, hn]
  push_cast
  field_simp

end Local

section Box

variable {F : Type} [Field F]

abbrev Idx {n : ℕ} (β : Fin n → ℕ) : Type := {p : Fin n × Fin n // β p.1 ≤ β p.2}

noncomputable def ext0 {n : ℕ} (β : Fin n → ℕ) : (Idx β → F) →+ Matrix (Fin n) (Fin n) F where
  toFun x := Matrix.of fun a b => if hab : β a ≤ β b then x ⟨(a, b), hab⟩ else 0
  map_zero' := by
    ext a b
    simp
  map_add' x y := by
    ext a b
    by_cases hab : β a ≤ β b <;> simp [hab]

theorem matrixExtendByZero_apply {n : ℕ} (β : Fin n → ℕ) (x : Idx β → F) (p : Idx β) :
    ext0 β x p.1.1 p.1.2 = x p := by
  have : β p.1.1 ≤ β p.1.2 := p.2
  simp [ext0, this]

theorem extendByZero_injective {n : ℕ} (β : Fin n → ℕ) : Function.Injective (ext0 (F := F) β) := by
  intro x y hxy
  funext p
  rw [← matrixExtendByZero_apply β x p, ← matrixExtendByZero_apply β y p, hxy]

theorem boxAdd_eq_map (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    boxAdd O β c =
      (AddSubgroup.pi Set.univ fun p : Idx β => line O (c p.1.1 p.1.2)).map (ext0 β) := by
  ext X
  constructor
  · rintro ⟨hX, hX'⟩
    refine AddSubgroup.mem_map.2 ⟨fun p => X p.1.1 p.1.2, ?_, ?_⟩
    · rw [AddSubgroup.mem_pi]
      intro p _
      exact mem_line.2 (hX' _ _)
    · ext a b
      by_cases hab : β a ≤ β b
      · simp [ext0, hab]
      · simp [ext0, hab, hX (not_le.1 hab)]
  · rintro h
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [AddSubgroup.mem_pi] at hx
    refine ⟨fun a b hab => ?_, fun a b => ?_⟩
    · simp [ext0, not_le.2 hab]
    · by_cases hab : β a ≤ β b
      · obtain ⟨o, ho, e⟩ := mem_line.1 (hx ⟨(a, b), hab⟩ (Set.mem_univ _))
        exact ⟨o, ho, by simpa [ext0, hab] using e⟩
      · exact ⟨0, O.zero_mem, by simp [ext0, hab]⟩

end Box

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (c c' : Fin n → Fin n → F), (∀ a b, c a b ≠ 0) → (∀ a b, c' a b ≠ 0) → (∀ a b, ∃ o ∈ O, c' a b = c a b * o) → (((boxAdd O β c').relIndex (boxAdd O β c) : ℕ) : ℝ) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => β p.1 ≤ β p.2), nrm (c p.1 p.2) / nrm (c' p.1 p.2) := by
  intro F _ _ _ _ O ϖ nrm q h n β c c' hc hc' hcc
  rw [boxAdd_eq_map, boxAdd_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (extendByZero_injective β),
    relIndex_pi', Nat.cast_prod,
    Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => β p.1 ≤ β p.2)
      (p := fun p : Fin n × Fin n => β p.1 ≤ β p.2) (fun p => by simp)]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨o, ho, e⟩ := hcc p.1.1 p.1.2
  have ho0 : o ≠ 0 := by
    rintro rfl
    exact hc' p.1.1 p.1.2 (by simpa using e)
  rw [e]
  exact relIndex_line h (hc _ _) ho ho0

end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentials
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ResKCoords

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem kaehler_atPrime_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by
    by_contra hc
    push_neg at hc
    exact (‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hle : Submonoid.powers t ≤ P.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)
  letI : Algebra (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle
  haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K A (Localization.Away t),
        ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P),
        ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P)
    (Submonoid.powers t) P.primeCompl hle
  haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization
      (P.primeCompl.map (algebraMap A (Localization.Away t)))
  haveI := h t ht
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  have r := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K)
    (S := Localization.Away t) D
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t)
    (Localization.AtPrime P)
  refine ⟨.of_equiv e, .equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]
  simp

theorem finitePresentation_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)) :
    Algebra.FinitePresentation K A := by
  refine RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)
  haveI := h r.1 r.2
  haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  rw [← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]
  exact (RingHom.finitePresentation_algebraMap).2 inferInstance

theorem finitePresentation_and_kaehler_atPrime :
    ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g →
      ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime],
      letI := secAlgebra g U.1
      Algebra.FinitePresentation K Γ(Y, U.1) ∧
        Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  intro K _ D Y g hg U P _
  letI := secAlgebra g U.1
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg
    ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)
  have key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t) := by
    intro t ht
    have h2 := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2
      _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]
    exact h2
  exact ⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩

end GlobalTheory.CompanionTheory.ResKCoords
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SphericalFunctionInvarianceProperties
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.SphLaw

theorem diag_mul {F : Type} [Field F] {c : ℕ} {a b : Matrix (Fin c) (Fin c) F}
    (ha : a.BlockTriangular id) (hb : b.BlockTriangular id) (i : Fin c) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · simp

theorem diag_ne_zero {F : Type} [Field F] {c : ℕ} (b : GL (Fin c) F)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) (i : Fin c) :
    (b : Matrix (Fin c) (Fin c) F) i i ≠ 0 := by
  have h : (b : Matrix (Fin c) (Fin c) F).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
  rw [Matrix.det_of_upperTriangular hb] at h
  exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)

noncomputable def wt {F : Type} [Field F] (nrm : AbsoluteValue F ℝ) {c : ℕ} (χ : Fin c → F → ℂ)
    (b : Matrix (Fin c) (Fin c) F) : ℂ :=
  ∏ i : Fin c, χ i (b i i) * ((nrm (b i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)

theorem chi_mul {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α) (i : Fin c)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : χ i (x * y) = χ i x * χ i y := by
  obtain ⟨e, he⟩ := hv x hx
  obtain ⟨e', he'⟩ := hv y hy
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := by omega
    positivity
  have hxy : nrm (x * y) = (q : ℝ) ^ (-(e + e')) := by
    rw [map_mul, he, he', neg_add, zpow_add₀ hq0]
  rw [hU.2 i _ _ hxy, hU.2 i _ _ he, hU.2 i _ _ he', zpow_add₀ (hU.1 i)]

theorem wt_mul {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α)
    (a b : GL (Fin c) F) (ha : (a : Matrix (Fin c) (Fin c) F).BlockTriangular id)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) :
    wt nrm χ ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) =
      wt nrm χ (a : Matrix (Fin c) (Fin c) F) * wt nrm χ (b : Matrix (Fin c) (Fin c) F) := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) i i =
      (a : Matrix (Fin c) (Fin c) F) i i * (b : Matrix (Fin c) (Fin c) F) i i := by
    rw [Units.val_mul]; exact diag_mul ha hb i
  rw [hd, chi_mul hq hv hU i (diag_ne_zero a ha i) (diag_ne_zero b hb i), map_mul,
    Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _)]
  push_cast
  ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → (∀ k ∈ GLint O c, φ k = 1) ∧ (∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g) ∧ (∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ g, φ (b * g) = φ b * φ g) ∧ Continuous φ ∧ ∀ φ', IsSphFn O nrm χ φ' → φ' = φ := by
  intro F _ _ _ _ O ϖ nrm q hLF c χ α hU φ hφ
  obtain ⟨hq, -, -, -, hv', -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) := fun x hx =>
    (hv' x hx).imp fun _ h => h.1
  have hIw := (GlobalTheory.T.iwasawa_decomposition_upperTriangular hLF) c
  have hKo : IsOpen (GLint O c : Set (GL (Fin c) F)) := (GlobalTheory.T.generalLinear_integral_compact_open hLF c).1
  have hval : ∀ (ψ : GL (Fin c) F → ℂ), IsSphFn O nrm χ ψ → ∀ b : GL (Fin c) F,
      (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
      ψ (b * k) = wt nrm χ (b : Matrix (Fin c) (Fin c) F) := fun ψ hψ b hb k hk => hψ b hb k hk
  have hone : (1 : GL (Fin c) F) ∈ GLint O c := one_mem _
  have h1t : ((1 : GL (Fin c) F) : Matrix (Fin c) (Fin c) F).BlockTriangular id := by
    simpa using (Matrix.blockTriangular_one (b := (id : Fin c → Fin c)) (R := F))
  have hb1 : ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id →
      φ b = wt nrm χ (b : Matrix (Fin c) (Fin c) F) := fun b hb => by
    simpa using hval φ hφ b hb 1 hone
  have hχ1 : ∀ i, χ i 1 = 1 := fun i => by
    have := hU.2 i 1 0 (by simp)
    simpa using this
  have hright : ∀ g, ∀ k ∈ GLint O c, φ (g * k) = φ g := by
    intro g k hk
    obtain ⟨b, hb, k', hk', rfl⟩ := hIw g
    rw [mul_assoc, hval φ hφ b hb _ ((GLint O c).mul_mem hk' hk), hval φ hφ b hb _ hk']
  refine ⟨?_, hright, ?_, ?_, ?_⟩
  · intro k hk
    have := hval φ hφ 1 h1t k hk
    rw [one_mul] at this
    rw [this]
    simp [wt, hχ1]
  · intro b hb g
    obtain ⟨b', hb', k, hk, rfl⟩ := hIw g
    have hbb : ((b * b' : GL (Fin c) F) : Matrix (Fin c) (Fin c) F).BlockTriangular id := by
      rw [Units.val_mul]; exact hb.mul hb'
    rw [← mul_assoc, hval φ hφ _ hbb k hk, hval φ hφ b' hb' k hk, hb1 b hb,
      wt_mul hq hv hU b b' hb hb']
  · refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (GLint O c : Set (GL (Fin c) F)),
      hKo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp [one_mem]
    · intro x hx
      have := hright g _ hx
      simpa using this
  · intro φ' hφ'
    funext g
    obtain ⟨b, hb, k, hk, rfl⟩ := hIw g
    rw [hval φ' hφ' b hb k hk, hval φ hφ b hb k hk]

end GlobalTheory.CompanionTheory.QL.SphLaw
end

