import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotLcAtAddOfIsNkltCentre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_lcAt_add_of_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  intro X _ _ _ p n hp hn Γ A z x hN hA hoff hzx hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hlcz := ((GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Γ + A) x z hzx).2 hlc)
  obtain ⟨E, η, m, g, hη, hm, hlog, hC, hd⟩ := hN
  obtain ⟨m₀, D₀, hm₀, hEff, rfl⟩ := hA
  obtain ⟨m', f, hm', hreg, heq⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p (qWeil D₀ m₀) ⟨m₀, D₀, hm₀, hEff, rfl⟩ z
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ :=
    GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Γ (qWeil D₀ m₀) η z m m' g f 1 hm hm' hlog heq
  rw [one_smul] at hlog''
  have h1 := ((GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Γ + qWeil D₀ m₀) η z m'' g'' hη hm'' hlog'').1 hlcz) E hC.1
  rw [hdisc E, one_mul] at h1
  have hf0 : 0 ≤ E.ord f := (E.ord_nonneg_iff f).2 (hC.1 _ hreg)
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have hfle : (E.ord f : ℚ) / m' ≤ 0 := by linarith
  have hfle' : (E.ord f : ℚ) ≤ 0 := by
    rwa [div_le_iff₀ hm'q, zero_mul] at hfle
  have hord : E.ord f = 0 := by
    have : E.ord f ≤ 0 := by exact_mod_cast hfle'
    omega
  have hreg' := hC.2 f hreg hord
  apply hoff
  intro w hw
  by_cases hc : Order.coheight w = 1
  · obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
    rw [heq w hw F hF]
    have a : 0 ≤ F.ord f :=
      (F.ord_nonneg_iff f).2 ((hF _).2 (regAt_of_specializes hw hreg))
    have b : 0 ≤ F.ord f⁻¹ :=
      (F.ord_nonneg_iff _).2 ((hF _).2 (regAt_of_specializes hw hreg'))
    rw [F.ord_inv] at b
    have : F.ord f = 0 := by omega
    simp [this]
  · have : D₀.mult w = 0 := by
      by_contra h
      exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    simp [qWeil, this]

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbIntAdSpanEqZero
section
open MeasureTheory GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM expG inG)

namespace GlobalTheory.PsCo.Pc1

theorem orbInt_adSpan_eq_zero : GlobalTheory.PsCo.Pc1.StOrbAd := by
  intro n ε μ _ s hs dt _ _ φ hφ
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant n ε μ
  have hp := isProperOrbit_realUJ hs
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hφ
    have hZ' : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
    obtain ⟨hc, hinv⟩ := GlobalTheory.expG_continuous_inv n ε Z hZ'
    obtain ⟨hsh, hd⟩ := GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan n ε Z H P hZ hH
    have hb : bas ε H P ∈ ShapeM ε P.totalDegree := Submodule.subset_span ⟨H, P, hH, le_rfl, rfl⟩
    obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hb
    obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hsh
    refine hasOrbInt_zero_of_hasDerivAt_conj (UJ ε) μ s hp dt (fun t => expG ε Z t) hc _ _ h1 h2 h3 h4 fun g u => ?_
    have e : ∀ v : ℝ, toM ((expG ε Z v)⁻¹ * g * expG ε Z v) =
        NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z) := fun v => by
      rw [← hinv v, ← Formalism.REAL.toM_expG ε Z v hZ']
      rfl
    simp only [e]
    exact hd (toM g) u
  | zero =>
    have h := (hp.hasOrbInt (dh := μ) (dt := dt) (f := fun _ => (0 : ℂ)) continuous_const HasCompactSupport.zero).smul 0
    rw [zero_mul, zero_smul] at h
    exact h
  | add φ ψ _ _ h1 h2 =>
    have h := h1.add h2
    rw [add_zero] at h
    exact h
  | smul a φ _ h1 =>
    have h := h1.smul a
    rw [mul_zero] at h
    exact h

end GlobalTheory.PsCo.Pc1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverage
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [mem_rStab]
  unfold avg
  simp only
  rw [hR, Subgroup.index_top]
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) :=
    ⟨⟨QuotientGroup.mk 1⟩, fun a => QuotientGroup.induction_on a fun x => QuotientGroup.eq.2 (Subgroup.mem_top _)⟩
  rw [finsum_unique]
  simp

variable {G : Type} [Group G]

theorem avg_cavg (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (f : G → ℂ) (p : P) :
    avg (fun k : K.subgroupOf P => cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G)) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
  have h : ∀ k : K.subgroupOf P, cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
    intro k
    have hk : ((k : P) : G) ∈ K := k.2
    unfold cavg
    rw [← avg_left (fun k' : K => f (((p : G) * k')⁻¹ * δ * ((p : G) * k'))) ⟨_, hk⟩]
    congr 1
    funext k'
    congr 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  simp_rw [h]
  exact avg_const _

theorem mem_twCent_sub (P : Subgroup G) (δ : G) (hδ : δ ∈ P) (x : P) :
    x ∈ twCent (MonoidHom.id P) ⟨δ, hδ⟩ ↔ (x : G) ∈ twCent (MonoidHom.id G) δ := by
  rw [mem_twCent, mem_twCent, Subtype.ext_iff]
  simp

theorem inf_eq_comap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (p : P) :
    twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).comap P.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map_equiv, mem_twCent_sub, MulAut.conj_symm_apply,
    Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map_sub (P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) :
    (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)).map P.subtype = cptPart (twCent (MonoidHom.id G) δ) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : P, IsCompact (closure (Subgroup.zpowers x : Set P)) ↔
      IsCompact (closure (Subgroup.zpowers (x : G) : Set G)) := by
    intro x
    rw [(hP.isClosedEmbedding_subtypeVal).isInducing.isCompact_iff,
      ← (hP.isClosedEmbedding_subtypeVal).closure_image_eq]
    have : (Subtype.val '' (Subgroup.zpowers x : Set P)) = (Subgroup.zpowers (x : G) : Set G) := by
      rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, MonoidHom.map_zpowers]
    first
      | (convert Iff.rfl using 3; exact this.symm)
      | (convert Iff.rfl using 3; exact this)
      | exact this ▸ Iff.rfl
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨(mem_twCent_sub P δ hδ x).1 hx, (hc x).1 hx'⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨⟨y, hT hy⟩, ⟨(mem_twCent_sub P δ hδ _).2 hy, (hc _).2 hy'⟩, rfl⟩

end GlobalTheory.IwRed

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (p : P) :
    (twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)) =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id G) δ)) := by
  rw [inf_eq_comap, Subgroup.relIndex_comap, cptPart_map_sub P hP δ hδ hT]

theorem summand_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (f : G → ℂ) (p : P) :
    summand (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun x : P => cavg K f (x : G)) p =
      summand (MonoidHom.id G) K δ f p := by
  unfold summand
  rw [relIndex_sub K P hP δ hδ hT p]
  congr 1
  simpa using avg_cavg K P δ hδ f p

def dcMap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) :
    DoubleCoset.Quotient (twCent (MonoidHom.id P) ⟨δ, hδ⟩ : Set P) (K.subgroupOf P : Set P) →
      DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (K : Set G) :=
  fun q => DoubleCoset.mk _ K ((Quotient.out q : P) : G)

theorem dcMap_bij (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (hT : twCent (MonoidHom.id G) δ ≤ P)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : Function.Bijective (dcMap K P δ hδ) := by
  constructor
  · intro q₁ q₂ h
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 h
    have htP : t ∈ P := hT ht
    have hkP : k ∈ P := by
      have : k = ((Quotient.out q₁ : P) : G)⁻¹ * t⁻¹ * ((Quotient.out q₂ : P) : G) := by rw [he]; group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem (Quotient.out q₁).2) (P.inv_mem htP)) (Quotient.out q₂).2
    rw [← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂, DoubleCoset.eq]
    refine ⟨⟨t, htP⟩, (mem_twCent_sub P δ hδ _).2 ht, ⟨k, hkP⟩, (Subgroup.mem_subgroupOf).2 hk, ?_⟩
    exact Subtype.ext (by simpa using he)
  · intro q
    obtain ⟨p, hp, k, hk, hg⟩ := hPK (Quotient.out q)
    refine ⟨DoubleCoset.mk _ _ (⟨p, hp⟩ : P), ?_⟩
    obtain ⟨t, ht, k', hk', he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (twCent (MonoidHom.id P) ⟨δ, hδ⟩) (K.subgroupOf P) (DoubleCoset.mk _ _ (⟨p, hp⟩ : P))).symm
    rw [← DoubleCoset.out_eq' _ _ q]
    show DoubleCoset.mk _ K _ = _
    rw [DoubleCoset.eq]
    refine ⟨(t : G)⁻¹, (twCent (MonoidHom.id G) δ).inv_mem ((mem_twCent_sub P δ hδ t).1 ht), ((k' : P) : G)⁻¹ * k,
      K.mul_mem (K.inv_mem ((Subgroup.mem_subgroupOf).1 hk')) hk, ?_⟩
    rw [hg]
    have he' := congrArg (fun x : P => (x : G)) he
    simp only [Subgroup.coe_mul] at he'
    rw [he']
    group

theorem twOrb_sub : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G),
    IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ,
    (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) →
    twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  intro G _ _ _ K P _ _ hP hPK δ hδ hT f _
  rw [twOrb_eq, twOrb_eq]
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij K P δ hδ hT hPK))]
  refine finsum_congr fun q => ?_
  rw [summand_sub K P hP δ hδ hT f]
  show summand _ K δ f (Quotient.out (DoubleCoset.mk _ K ((Quotient.out q : P) : G))) = _
  obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
    (DoubleCoset.out_eq' (twCent (MonoidHom.id G) δ) K (DoubleCoset.mk _ K ((Quotient.out q : P) : G))).symm
  rw [he, summand_rep _ K δ f _ ht hk]

end GlobalTheory.IwRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqWeightedLatticeOrbitCount
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbReindex

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) (y : A) :
    y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [LinearMap.mulLeft_apply, Units.inv_mul_cancel_left] using hx
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, Units.mul_inv_cancel_left]⟩

theorem stabLat_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) :
    GlobalTheory.UnitLemma.stabLat O (GlobalTheory.UnitLemma.mulLat O (t : A) L) = GlobalTheory.UnitLemma.stabLat O L := by
  ext s
  change (∀ y, y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ (s : A) * y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L) ↔
    (∀ y, y ∈ L ↔ (s : A) * y ∈ L)
  simp only [mem_mulLat_unit]
  constructor
  · intro h y
    have e : ((t⁻¹ : Aˣ) : A) * ((s : A) * ((t : A) * y)) = (s : A) * y := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    have := h ((t : A) * y)
    rwa [Units.inv_mul_cancel_left, e] at this
  · intro h y
    rw [h (((t⁻¹ : Aˣ) : A) * y), mul_left_comm]

theorem cast_finsum_rat {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · simpa using map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support (fun a => ((u a : ℚ) : ℂ))).Finite := by
      have : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u := by
        ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.OrbReindex

namespace GlobalTheory.OrbReindex
open GlobalTheory.UnitLemma

theorem finsum_ite_subtype {α : Type*} (p : α → Prop) (c : α → ℂ) :
    (∑ᶠ q, if p q then c q else 0) = ∑ᶠ s : {q // p q}, c s.1 := by
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]

theorem twOrb_eq_orbSum : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  intro G _ _ Kg δ f O A _ _ _ Tb X M τ hK hinj hsurj hT hTs havg hidx

  have hX : ∀ h ∈ twCent (MonoidHom.id G) δ, ∀ g : G, (M (h * g) ∈ X ↔ M g ∈ X) := by
    intro h hh g
    have hc : h * δ = δ * h := hh
    have hc' : h⁻¹ * δ * h = δ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have e : avg (fun k : Kg => f ((h * g * k)⁻¹ * δ * (MonoidHom.id G) (h * g * k))) =
        avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) := by
      congr 1
      funext k
      congr 1
      simp only [MonoidHom.id_apply]
      calc (h * g * (k : G))⁻¹ * δ * (h * g * k) = (g * (k : G))⁻¹ * (h⁻¹ * δ * h) * (g * k) := by group
        _ = _ := by rw [hc']
    have := (havg (h * g)).symm.trans (e.trans (havg g))
    by_cases a : M (h * g) ∈ X <;> by_cases b : M g ∈ X <;> simp_all
  let r : X → X → Prop := fun L L' => ∃ t ∈ Tb, (L' : Submodule O A) = mulLat O (t : A) (L : Submodule O A)
  have hw : ∀ L L' : X, Relation.EqvGen r L L' → stabLat O L.1 = stabLat O L'.1 := by
    intro L L' h
    induction h with
    | rel a b hab =>
      obtain ⟨t, -, ht⟩ := hab
      rw [ht, stabLat_mulLat_unit]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} → Orb O Tb X := fun q => Quot.mk r ⟨M (Quotient.out q.1), q.2⟩
  let ψ : Orb O Tb X → DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) :=
    Quot.lift (fun L : X => DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj L.1 L.2))) (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨t, ht, hLL⟩
      obtain ⟨h, hh, rfl⟩ := hTs t ht
      have hg := Classical.choose_spec (hsurj L hL)
      have hg' := Classical.choose_spec (hsurj L' hL')
      set g := Classical.choose (hsurj L hL)
      set g' := Classical.choose (hsurj L' hL')
      have hMM : M (h * g) = M g' := by
        rw [(hT h hh).2, hg, hg']
        exact hLL.symm
      have hk := hinj _ _ hMM
      show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g = DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g'
      rw [DoubleCoset.eq]
      exact ⟨h, hh, _, hk, by group⟩)
  have hleft : ∀ q : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, ψ (φ q) = q.1 := by
    intro q
    show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj (M (Quotient.out q.1)) q.2)) = q.1
    have hg := Classical.choose_spec (hsurj (M (Quotient.out q.1)) q.2)
    set g := Classical.choose (hsurj (M (Quotient.out q.1)) q.2)
    have hk := hinj _ _ hg.symm
    rw [← DoubleCoset.out_eq' (twCent (MonoidHom.id G) δ) Kg q.1, DoubleCoset.eq]
    exact ⟨1, (twCent (MonoidHom.id G) δ).one_mem, _, Kg.inv_mem hk, by group⟩
  have hinjφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    rw [← hleft a, ← hleft b, hab]
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨L, hL⟩
    obtain ⟨g, rfl⟩ := hsurj L hL
    obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id G) δ) Kg g
    have hM : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) = mulLat O (τ h : A) (M g) := by
      rw [hout, hK _ _ hk, (hT h hh).2]
    have hmem : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) ∈ X := by
      rw [hout, hK _ _ hk, hX h hh]
      exact hL
    refine ⟨⟨DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g, hmem⟩, ?_⟩
    exact (Quot.sound ⟨τ h, (hT h hh).1, hM⟩).symm
  let e : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} ≃ Orb O Tb X := Equiv.ofBijective φ ⟨hinjφ, hsurjφ⟩

  have hwt : ∀ s : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, stabLat O (Quot.out (e s)).1 = stabLat O (M (Quotient.out s.1)) := by
    intro s
    have h1 : Quot.mk r (Quot.out (φ s)) = φ s := Quot.out_eq _
    exact hw _ _ (Quot.eqvGen_exact h1)
  unfold twOrb orbSum
  simp only [havg, hidx]
  rw [cast_finsum_rat, ← finsum_comp_equiv e]
  simp only [hwt, one_mul, mul_ite, mul_one, mul_zero]
  simp only [Rat.cast_natCast]
  exact finsum_ite_subtype _ _

end GlobalTheory.OrbReindex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndex
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.OrbIndUnit

theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))
  rw [finsum_unique]
  simp

theorem twOrb_id_indicator (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  unfold twOrb
  apply finsum_congr
  intro q
  set Q : G := Quotient.out q with hQ
  have hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k)))
      = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q) := by
    funext k
    have he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k := by
      simp only [MonoidHom.id_apply]; group
    rw [he]
    by_cases h : Q⁻¹ * γ * Q ∈ K
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
      simp [Set.indicator_apply, h, h']
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K := by
        intro h'
        apply h
        have := K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)
        simpa [mul_assoc] using this
      simp [Set.indicator_apply, h, h']
  rw [hfun, avg_const_fun]
  by_cases h : Q⁻¹ * γ * Q ∈ K
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

end GlobalTheory.OrbIndUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalProjectionIntegralAdicStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_projection_integral_adic : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    (e : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, Valued.v (e i j) ≤ 1) → (∀ x, e *ᵥ x ∈ V) →
    (∀ x ∈ V, e *ᵥ x = x) → (∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) →
    ∃ (s : ℕ) (f : Module.Basis (Fin s) (w.adicCompletion E) V),
      Valued.v (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → w.adicCompletion E) k) * (f j : Fin n → w.adicCompletion E) k).det = 1 := by
  first | exact @GlobalTheory.IdempotentUnimodular.main | exact GlobalTheory.IdempotentUnimodular.main | (intros; apply GlobalTheory.IdempotentUnimodular.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffCurvatureCompHolomorphicStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_curvature_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  first | exact @GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | exact GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | (intros; apply GlobalTheory.GoodTop.mixTop_curvAt_comp_holo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinearStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_position_linear : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r) (s t : ℂ) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  first | exact @GlobalTheory.GoodTop.mixTop_position_linear | exact GlobalTheory.GoodTop.mixTop_position_linear | (intros; apply GlobalTheory.GoodTop.mixTop_position_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIffStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w m → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  first | exact @GlobalTheory.congConj_iff | exact GlobalTheory.congConj_iff | (intros; apply GlobalTheory.congConj_iff <;> assumption)
end

