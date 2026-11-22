import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

noncomputable section
namespace GlobalTheory.HeckeCount
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pLat (D : Datum H) (p : ℕ) : AddSubgroup D.La := (DistribMulAction.toAddMonoidHom D.La p).range

theorem mem_pLat {D : Datum H} {p : ℕ} {a : D.La} : a ∈ pLat D p ↔ ∃ b, a = p • b := by
  simp [pLat, eq_comm]

def LatCount (D : Datum H) (p : ℕ) (J : Ideal (𝓞 E)) (m : ℕ) : Type :=
  {N : AddSubgroup D.La // pLat D p ≤ N ∧ (∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) ∧
    (∀ a ∈ J, ∀ x ∈ N, a • x ∈ pLat D p) ∧ (pLat D p).relIndex N = m}

section Alg
variable {D : Datum H} {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)

def evA (p : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev p a)) fun a b => by rw [I.add]; rfl

theorem ker_evA {p : ℕ} (hp : 0 < p) : (evA I p).ker = pLat D p := by
  ext a
  rw [AddMonoidHom.mem_ker, mem_pLat, ← I.ker p hp a]
  exact ofMul_eq_zero

theorem relIndex_eq {p : ℕ} (hp : 0 < p) (N : AddSubgroup D.La) :
    (pLat D p).relIndex N = Nat.card (N.map (evA I p)) := by
  rw [← ker_evA I hp, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddMonoidHom.comap_ker,
    AddSubgroup.index_ker, AddMonoidHom.range_comp, AddSubgroup.range_subtype]

end Alg
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
section Alg2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)

theorem card_toAdd (C : Subgroup Q) : Nat.card C.toAddSubgroup = Nat.card C :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun _ => Iff.rfl)

def datumEquiv {p : ℕ} (hp : 0 < p) (hnat : ∀ x, act (p : 𝓞 E) x = x ^ p) {J : Ideal (𝓞 E)}
    (hpJ : (p : 𝓞 E) ∈ J) {m : ℕ} (hm : m ≠ 0) :
    {C₀ : Subgroup Q // (∀ a, ∀ x ∈ C₀, act a x ∈ C₀) ∧ (∀ x ∈ C₀, ∀ a ∈ J, act a x = 1) ∧ Finite C₀ ∧
      Nat.card C₀ = m} ≃ LatCount D p J m where
  toFun C := ⟨C.1.toAddSubgroup.comap (evA I p), by
      rw [← ker_evA I hp]; exact AddMonoidHom.ker_le_comap _ _,
    fun a x hx => by
      show (I.ev p (a • x)) ∈ C.1
      rw [I.lin]; exact C.2.1 a _ hx,
    fun a ha x hx => by
      rw [← ker_evA I hp, AddMonoidHom.mem_ker]
      show Additive.ofMul (I.ev p (a • x)) = 0
      rw [I.lin, show act a (I.ev p x) = 1 from C.2.2.1 _ hx a ha]; rfl,
    by
      have hle : C.1.toAddSubgroup ≤ (evA I p).range := fun x hx => by
        have h1 : x.toMul ^ p = 1 := (hnat _).symm.trans (C.2.2.1 _ hx _ hpJ)
        obtain ⟨a, ha⟩ := (I.onto p hp _).1 h1
        exact ⟨a, ha⟩
      rw [relIndex_eq I hp, AddSubgroup.map_comap_eq, inf_eq_right.2 hle, card_toAdd]
      exact C.2.2.2.2⟩
  invFun N := ⟨Subgroup.toAddSubgroup.symm (N.1.map (evA I p)), by
      rintro a _ ⟨x, hx, rfl⟩
      exact ⟨a • x, N.2.2.1 a x hx, I.lin p a x⟩,
    by
      rintro _ ⟨x, hx, rfl⟩ a ha
      have h := N.2.2.2.1 a ha x hx
      rw [← ker_evA I hp, AddMonoidHom.mem_ker] at h
      show act a (I.ev p x) = 1
      rw [← I.lin]; exact h,
    by
      have : Nat.card (Subgroup.toAddSubgroup.symm (N.1.map (evA I p))) ≠ 0 := by
        rw [← card_toAdd, OrderIso.apply_symm_apply, ← relIndex_eq I hp, N.2.2.2.2]; exact hm
      exact Nat.finite_of_card_ne_zero this,
    by rw [← card_toAdd, OrderIso.apply_symm_apply, ← relIndex_eq I hp]; exact N.2.2.2.2⟩
  left_inv C := by
    apply Subtype.ext
    show Subgroup.toAddSubgroup.symm _ = C.1
    rw [AddSubgroup.map_comap_eq, OrderIso.symm_apply_eq]
    refine inf_eq_right.2 fun x hx => ?_
    have h1 : x.toMul ^ p = 1 := (hnat _).symm.trans (C.2.2.1 _ hx _ hpJ)
    obtain ⟨a, ha⟩ := (I.onto p hp _).1 h1
    exact ⟨a, ha⟩
  right_inv N := by
    apply Subtype.ext
    show AddSubgroup.comap (evA I p) (Subgroup.toAddSubgroup (Subgroup.toAddSubgroup.symm (N.1.map (evA I p)))) = N.1
    rw [OrderIso.apply_symm_apply, AddSubgroup.comap_map_eq, ker_evA I hp]
    exact sup_eq_left.2 N.2.1

end Alg2
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

section Fibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
  [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}

include hL in

theorem map_pow_eq (h : IsSplitPrimeOff l p P) {i : ℕ} {C : Subgroup (Pts o.t)}
    (hC : o.t.HeckeKer (𝟙_ _) D P p i C) {C₀ : Subgroup (Pts o.t)} (h₀ : IsHeckeDatum o.t P i C₀)
    (e : (C : Set (Pts o.t)) = heckeKernel o.t p P C₀) : C.map (powMonoidHom p) = C₀ := by
  have hcard : Nat.card (C.map (powMonoidHom p)) = Ideal.absNorm P ^ i := by
    obtain ⟨-, -, -, -, c₅, c₆⟩ := hC
    obtain ⟨-, -, hp, -, -⟩ := (splitPrime_iff l p P).1 h
    obtain ⟨-, -, hc⟩ := tate_facts hL o
    have hpos := pow_pos hp.pos (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))
    have hm := card_eq_tors_mul C p
    rw [card_tors, card_inter_tors, hc p hp.pos] at c₆
    rw [c₅] at hm
    have h₁ := mul_ne_zero_iff.1 (hm ▸ hpos.ne')
    exact mul_left_cancel₀ h₁.1 (hm.symm.trans c₆)
  have : Finite C₀ := h₀.2.2.1
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, h₀.2.2.2])
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ heckeKernel o.t p P C₀ := e ▸ hx
  obtain ⟨x₁, x₂, x₃, rfl, ⟨t₁, -⟩, ⟨-, k₂⟩, ⟨t₃, -⟩⟩ := hx'
  show (x₁ * x₂ * x₃) ^ p ∈ C₀
  rw [mul_pow, mul_pow, t₁, t₃, _root_.one_mul, _root_.mul_one]
  exact k₂

include hL in
theorem isHeckeDatum_map_pow (h : IsSplitPrimeOff l p P) {i : ℕ} {C : Subgroup (Pts o.t)}
    (hC : o.t.HeckeKer (𝟙_ _) D P p i C) : IsHeckeDatum o.t P i (C.map (powMonoidHom p)) := by
  obtain ⟨C₀, h₀, e⟩ := (heckeKer_iff hL o h i C).1 hC
  rw [map_pow_eq hL o h hC h₀ e]
  exact h₀

def heckeKerEquivDatum (h : IsSplitPrimeOff l p P) (i : ℕ) :
    {C : Subgroup (Pts o.t) // o.t.HeckeKer (𝟙_ _) D P p i C} ≃
      {C₀ : Subgroup (Pts o.t) // IsHeckeDatum o.t P i C₀} where
  toFun C := ⟨C.1.map (powMonoidHom p), isHeckeDatum_map_pow hL o h C.2⟩
  invFun C₀ := ⟨(exists_heckeKer_of_datum hL o h C₀.2).choose,
    (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.2⟩
  left_inv C := by
    apply Subtype.ext
    apply SetLike.coe_injective
    obtain ⟨C₀, h₀, e⟩ := (heckeKer_iff hL o h i C.1).1 C.2
    have hm := map_pow_eq hL o h C.2 h₀ e
    refine (exists_heckeKer_of_datum hL o h (isHeckeDatum_map_pow hL o h C.2)).choose_spec.1.trans ?_
    simp only [hm]
    exact e.symm
  right_inv C₀ := by
    apply Subtype.ext
    exact map_pow_eq hL o h (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.2 C₀.2
      (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.1

end Fibre
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

section Fibre2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
  [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}

include hL in
theorem nonempty_datum_equiv (h : IsSplitPrimeOff l p P) (i : ℕ) :
    Nonempty ({C₀ : Subgroup (Pts o.t) // IsHeckeDatum o.t P i C₀} ≃
      LatCount D p (conjIdeal H P) (Ideal.absNorm P ^ i)) := by
  obtain ⟨hP, -, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
  obtain ⟨⟨I⟩, -, -⟩ := tate_facts hL o
  have h0 : Ideal.absNorm P ≠ 0 := fun e => by
    rw [Ideal.absNorm_eq_zero_iff.1 e] at hpP
    exact Nat.cast_ne_zero.2 hp.pos.ne' (Ideal.mem_bot.1 hpP)
  exact ⟨(Equiv.subtypeEquivRight fun C₀ => Iff.rfl).trans
    (datumEquiv I hp.pos (fun x => (isAct_ptAct o.t _).nat p x) (natCast_mem_conj hpP) (pow_ne_zero i h0))⟩

end Fibre2

section Transfer2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} {k : Type} [Field k]
  {s : Sp k ⟶ Sp B}

theorem nonempty_transfer_equiv (u : Obj D l b sX) {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y)
    (P : Ideal (𝓞 E)) (p i : ℕ) :
    Nonempty ({C' : Subgroup (Pts o.t) // o.t.HeckeKer (𝟙_ _) D P p i C'} ≃
      {C : Subgroup (Over.mk y ⟶ u.t.G) // u.t.HeckeKer (Over.mk y) D P p i C}) := by
  obtain ⟨ρ, -, e₀, -⟩ := exists_fibre_equiv u m
  have hx : ∀ (x : Pts o.t) (x₀ : Over.mk y ⟶ u.t.G), x₀.left = x.left ≫ m.cm.F → x₀ = ρ x := fun x x₀ h =>
    Over.OverMorphism.ext (h.trans (e₀ x).symm)
  have same : ∀ C : Subgroup (Over.mk y ⟶ u.t.G), SamePoints m (C.comap ρ.toMonoidHom : Set (Pts o.t)) C :=
    fun C x x₀ h => by rw [hx x x₀ h]; rfl
  refine ⟨{ toFun := fun C' => ⟨C'.1.map ρ.toMonoidHom, ?_⟩
            invFun := fun C => ⟨C.1.comap ρ.toMonoidHom, (heckeKer_transfer m (same C.1) P p i).1 C.2⟩
            left_inv := fun C' => Subtype.ext (Subgroup.comap_map_eq_self_of_injective ρ.injective _)
            right_inv := fun C => Subtype.ext (Subgroup.map_comap_eq_self_of_surjective ρ.surjective _) }⟩
  refine (heckeKer_transfer m (same _) P p i).2 ?_
  rw [Subgroup.comap_map_eq_self_of_injective ρ.injective]
  exact C'.2

end Transfer2
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

theorem card_hkKer_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (q i : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P q → ∃ n : ℕ, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
      (z : FrPt Xo c Ω), Nonempty (Fin n ≃ hkKer (Xo := Xo) P q i Ω z) := by
  intro E _ _ _ H Dw l Xo c P q i hP
  refine ⟨Nat.card (LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)), fun Ω _ _ _ z => ?_⟩
  have hs : IsSplitPrimeOff l q P := (splitPrime_iff l q P).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hP)
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (z.x ≫ Xo.s)).hom.injective
  obtain ⟨o, ⟨m⟩⟩ := exists_fibre_obj Xo z.x z.x rfl
  obtain ⟨eT⟩ := nonempty_transfer_equiv Xo.univ m P q i
  obtain ⟨eL⟩ := nonempty_datum_equiv GlobalTheory.firstFiveLaws.1 o hs i
  let e : hkKer (Xo := Xo) P q i Ω z ≃ LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i) :=
    eT.symm.trans ((heckeKerEquivDatum GlobalTheory.firstFiveLaws.1 o hs i).trans eL)
  have : Finite (hkKer (Xo := Xo) P q i Ω z) :=
    GlobalTheory.HeckePointLaw.finite_heckeKer hs.1.pos hs.2.2.1 i z.x
  have : Finite (LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)) := Finite.of_equiv _ e
  exact ⟨(Finite.equivFin _).symm.trans e.symm⟩

end GlobalTheory.HeckeCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicSubLtOne
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

section Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tr {F1 : Subfield E} (h : F1 = maximalRealSubfield E) : AL E →+* E ⊗[F1] Formalism.L2.Herm.Af F1 :=
  (GlobalTheory.LevSplit.swp F1 E).comp (GlobalTheory.Mem.R3.swapCast h).symm.toRingHom

theorem tr_rfl (z : AL E) : tr (rfl : maximalRealSubfield E = maximalRealSubfield E) z = z := by
  exact (Algebra.TensorProduct.comm _ _ _).apply_symm_apply z

theorem tr_int {F1 : Subfield E} (h : F1 = maximalRealSubfield E) {z : AL E} (hz : z ∈ ALint E) :
    tr h z ∈ Formalism.L2.Herm.intAf F1 E := by
  subst h
  rw [tr_rfl]
  have key : ReciprocityTheory.Aut.ALint E ≤ Formalism.L2.Herm.intAf (maximalRealSubfield E) E := by
    unfold ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact key hz

theorem proj_le_one (s : SplitPlace E) {z : AL E} (hz : z ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E) :
    Valued.v (s.proj z) ≤ 1 := by
  have key : Formalism.L2.Herm.intAf (maximalRealSubfield E) E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield E)).toSubring.comap s.proj := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring,
        IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact s.split_le_one b
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  have := key hz
  rwa [Subring.mem_comap, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem res_eq {F1 : Subfield E} (h : F1 = maximalRealSubfield E) (s : SplitPlace E) (z : AL E)
    (y : Formalism.L2.Herm.intAf F1 E) (hy : (y : E ⊗[F1] Formalism.L2.Herm.Af F1) = tr h z) (a : 𝓞 E)
    (ha : Valued.v (s.proj z - s.i (a : E)) < 1) : resS F1 s.w y = Ideal.Quotient.mk _ a := by
  subst h
  have key : ∀ (t : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E))
      (ht : t ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E),
      ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c := by
    intro t ht
    refine Subring.closure_induction
      (p := fun t ht => ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c) ?_ ?_ ?_ ?_ ?_ ?_ ht
    · rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · refine ⟨b, ?_, ?_⟩
        · simp [ReciprocityTheory.Aut.SplitPlace.proj]
        · have e : (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.oToS (maximalRealSubfield E) E b :=
            Subtype.ext (Formalism.L2.DIV.oToS_coe (F := maximalRealSubfield E) b).symm
          rw [e, Formalism.L2.DIV.resS_oToS]
      · obtain ⟨D0, hD0, hD0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.v.ne_bot
        obtain ⟨r, hr⟩ := Formalism.UG.P.csApprox_local s.v D0 hD0ne (a s.v) (ha s.v)
        have hlt : s.v.intValuation D0 < 1 := by
          exact (s.v.intValuation_lt_one_iff_mem D0).mpr hD0
        have hi : s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E)) : E) =
            algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r := by
          rw [ReciprocityTheory.Aut.split_coe_algebraMap, AlgHom.commutes,
            IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
              (s.v.adicCompletion (maximalRealSubfield E)) r]
        refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r, ?_, ?_⟩
        · have hp : s.proj ((1 : E) ⊗ₜ[maximalRealSubfield E] a) = a s.v := by
            simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.lift_tmul, map_one, one_mul]
            rfl
          rw [hp, hi]
          exact hr.trans hlt
        · have hsplit : (⟨_, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.adS (maximalRealSubfield E) E (⟨a, ha⟩ - Formalism.L2.DIV.oToAd (maximalRealSubfield E) r) +
                Formalism.L2.DIV.oToS (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r) := by
            rw [← Formalism.L2.DIV.adS_oToAd, ← map_add, sub_add_cancel]
            exact Subtype.ext (Formalism.L2.DIV.adS_coe (E := E) ⟨a, ha⟩).symm
          rw [hsplit, map_add, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_adS_eq_zero s.w s.v s.w_under.symm, zero_add]
          show Valued.v (a s.v - algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r) < 1
          exact hr.trans hlt
    · refine ⟨0, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 0 = _
      simp
    · refine ⟨1, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 1 = _
      simp
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 + c2, ?_, ?_⟩
      · have : s.proj (x + y) - s.i ((c1 + c2 : 𝓞 E) : E) = (s.proj x - s.i (c1 : E)) + (s.proj y - s.i (c2 : E)) := by
          push_cast
          rw [map_add, map_add]
          ring
        rw [this]
        exact Valuation.map_add_lt _ h1 h2
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ + ⟨y, hy⟩) = _
        rw [map_add, e1, e2, map_add]
    · rintro x hx ⟨c1, h1, e1⟩
      refine ⟨-c1, ?_, ?_⟩
      · have : s.proj (-x) - s.i ((-c1 : 𝓞 E) : E) = -(s.proj x - s.i (c1 : E)) := by
          push_cast
          rw [map_neg, map_neg]
          ring
        rw [this, Valuation.map_neg]
        exact h1
      · change resS (maximalRealSubfield E) s.w (-⟨x, hx⟩) = _
        rw [map_neg, e1, map_neg]
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 * c2, ?_, ?_⟩
      · have : s.proj (x * y) - s.i ((c1 * c2 : 𝓞 E) : E) =
            s.proj x * (s.proj y - s.i (c2 : E)) + (s.proj x - s.i (c1 : E)) * s.i (c2 : E) := by
          push_cast
          rw [map_mul, map_mul]
          ring
        rw [this]
        have hx1 : Valued.v (s.proj x) ≤ 1 := proj_le_one s hx
        have hc2 : Valued.v (s.i (c2 : E)) ≤ 1 := s.split_le_one c2
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' hx1) h2
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_right' hc2) h1
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ * ⟨y, hy⟩) = _
        rw [map_mul, e1, e2, map_mul]
  obtain ⟨c, hc1, hc2⟩ := key y.1 y.2
  have hyz : (y : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E)) = z := by rw [hy, tr_rfl]
  rw [hyz] at hc1
  have hca : Valued.v (s.i ((c - a : 𝓞 E) : E)) < 1 := by
    have : s.i ((c - a : 𝓞 E) : E) = (s.proj z - s.i (a : E)) - (s.proj z - s.i (c : E)) := by
      push_cast
      rw [map_sub]
      ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hc1)
  have hmem : c - a ∈ s.w.asIdeal := (s.split_mem_ideal (c - a)).mpr hca
  have hyy : (⟨y.1, y.2⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) = y := rfl
  rw [hyy] at hc2
  rw [hc2]
  exact Ideal.Quotient.eq.mpr hmem

end Res

section Padic

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {g : ℕ} [Fact g.Prime]

end Padic

end GlobalTheory.RowGood

end

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

end GlobalTheory.RowGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.IdemSumBranch

open GlobalTheory.StdFrames GlobalTheory.IdemSupport

variable {D : D7}

theorem cpt_idemSum {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {Q : Pl D.host.E} (hQ : Q ∈ S) :
    cpt Q (toEAf D ea) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hs := map_sum ((cpt Q).comp (toEAf D)).toAddMonoidHom es S
  refine hs.trans ?_
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · exact (cpt_of_isIdemAt (hes Q hQ)).1
  · intro R hR hne
    exact (cpt_of_isIdemAt (hes R hR)).2 Q hne.symm

theorem conjPrime_ne {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {P Q : Pl D.host.E} (hP : P ∈ S)
    (hQ : Q ∈ S) : cP Q ≠ P := by
  intro hc
  have h1 := congrArg (fun t => cpt P (toEAf D t)) h.2
  simp only [RingHom.map_mul, RingHom.map_zero, cpt_idemSum h hP, one_mul] at h1
  rw [toEAf_cA, ← hc] at h1
  have h2 := cpt_sg_eq_zero h1
  rw [sg_sg, cpt_idemSum h hQ] at h2
  exact one_ne_zero h2

theorem branch : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)),
    IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧
      infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  intro D P e f ea S h1 hS hP
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem (comp_toAd D) h1
  have hinf : infPart D f = 0 := hf ▸ (place_comp (comp_toAd D) hε).1
  rcases h1 with ⟨h1, h2⟩ | ⟨rfl, -⟩
  · refine ⟨h1, h2, ?_, hinf, fun Q hQ => conjPrime_ne hS hP hQ⟩
    rw [h2, RingHom.map_add, Formalism.L2.Theta.cA_cA, add_comm]
  · exfalso
    have h2 := (place_comp (comp_toAd D) hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ (conjPrime_ne hS hP hP)] at h2
    exact zero_ne_one h2

end GlobalTheory.IdemSumBranch
end

