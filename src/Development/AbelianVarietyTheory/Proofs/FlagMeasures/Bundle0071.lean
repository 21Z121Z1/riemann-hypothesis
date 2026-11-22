import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometries
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMove

section

variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]

theorem discN_congr {V W : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (k : W →ₗ⋆[K] W →ₗ[K] K) (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (A : Submodule R V) (B : Submodule R W)
    (hAB : ∀ x, e x ∈ B ↔ x ∈ A) : discN k B = discN h A := by
  have hd : ∀ x, e x ∈ dual k B ↔ x ∈ dual h A := by
    intro x
    unfold dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    constructor
    · intro H y hy
      rw [← he]
      exact H _ ((hAB y).2 hy)
    · intro H y hy
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [he]
      exact H _ ((hAB z).1 hy)
  have hm : ∀ (A : Submodule R V) (B : Submodule R W), (∀ x, e x ∈ B ↔ x ∈ A) →
      B.toAddSubgroup = A.toAddSubgroup.map (e : V →+ W) := by
    intro A B H
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · intro hy
      exact ⟨z, (H z).1 hy, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : e w = e z := hwz
      rw [← this]
      exact (H w).2 hw
  unfold discN idxN
  rw [hm A B hAB, hm _ _ hd]
  exact AddSubgroup.relIndex_map_map_of_injective (f := (e : V →+ W)) _ _ e.injective

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem smul_mem_smul_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V) (x : V) :
    (g : V ≃ₗ[K] V) x ∈ g • L ↔ x ∈ L := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    have : w = x := (g : V ≃ₗ[K] V).injective hwx
    exact this ▸ hw
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem smul_mem_primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V)
    (U : Submodule K V) (j n : ℕ) : g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n := by
  let e : U ≃ₗ[K] (g • U : Submodule K V) := (g : V ≃ₗ[K] V).submoduleMap U
  have he : ∀ x : U, (e x : V) = (g : V ≃ₗ[K] V) x := fun _ => rfl
  have h1 : Module.finrank K (g • U : Submodule K V) = Module.finrank K U := e.finrank_eq.symm
  have h2 : discN (hRes h (g • U)) (latIn (g • U) (g • L)) = discN (hRes h U) (latIn U L) := by
    refine discN_congr _ _ e (fun x y => ?_) _ _ (fun x => ?_)
    · exact g.2 (x : V) (y : V)
    · exact smul_mem_smul_iff h g L (x : V)
  change _ ∧ _ ↔ _ ∧ _
  rw [h1, h2]

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ g L U j n
  refine ⟨smul_mem_primSp h g L U j n, ?_⟩
  have hi : primSp h (g • L) j n = (fun W : Submodule K V => g • W) '' primSp h L j n := by
    ext W
    constructor
    · intro hW
      refine ⟨g⁻¹ • W, ?_, smul_inv_smul g W⟩
      rw [← smul_mem_primSp h g, smul_inv_smul]
      exact hW
    · rintro ⟨W', hW', rfl⟩
      exact (smul_mem_primSp h g L W' j n).2 hW'
  rw [hi]
  exact (MulAction.injective g).encard_image _

end GlobalTheory.Mass.PrimMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexEqCardMap
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LevelFamilies

theorem relIndex_eq_card_map {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl

theorem ncard_classes {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M B A : Submodule O V) (hMB : M ≤ B) (hBA : B ≤ A) [Finite (A.map M.mkQ)] :
    Set.ncard {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      Nat.card (A.map M.mkQ) - Nat.card (B.map M.mkQ) := by
  have hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) := by
    intro c c' h
    obtain ⟨v, rfl⟩ := M.mkQ_surjective c
    have : v ∈ (M.mkQ ⁻¹' {c'} : Set V) := by
      have h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'} := h
      rw [← h']; simp
    simpa using this
  have hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M} := by
    intro y
    ext x
    simp [Submodule.Quotient.eq]
  have hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B := by
    intro y
    constructor
    · rintro ⟨b, hb, hby⟩
      have h1 : b - y ∈ M := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y = b - (b - y) := by abel
      rw [h2]
      exact B.sub_mem hb (hMB h1)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) ''
        ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M))) := by
    ext C
    constructor
    · rintro ⟨y, hyA, hyB, rfl⟩
      exact ⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩
    · rintro ⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩
      exact ⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩
  have hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M)) :=
    Submodule.map_mono hBA
  have hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite := Set.toFinite _
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]
  rfl

theorem two_le_resQ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : 2 ≤ resQ ϖ := by
  have h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := hϖ.maximalIdeal_eq.symm
  have h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [h]
    rfl
  rw [h1]
  exact Finite.one_lt_card

theorem exists_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.TypeBe d Λ → ∃ i J i' : ℕ, 1 ≤ i ∧ (i : ℤ) ≤ S.a ∧ 1 ≤ J ∧ J ≤ r ∧ i' < i ∧ S.InFF (S.q ^ i) J (S.q ^ i - S.q ^ i') d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB
  obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hMA : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hq : 2 ≤ S.q := two_le_resQ S.ϖ S.ϖ_irr
  have hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i := by
    rw [← hbe, ← relIndex_eq_card_map]; rfl
  haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    positivity

  let P : ℕ → Prop := fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j
  obtain ⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by
    by_contra h
    push_neg at h
    exact hB.1 (le_antisymm hMA h)
  let J := Nat.findGreatest P r
  have hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := fun y hy =>
    Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩
  have hPJ : P J := Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hJ1 : 1 ≤ J := by
    have h1 : S.levC d Λ y0 ≠ 0 := fun h => hy0M ((hlev0 y0 hy0A).1 h)
    have := hle y0 hy0A
    omega

  let B : Submodule L.O S.V := S.sat Λ ⊓
    ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)
  have hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1 := by
    intro y hy
    rw [hlev y hy]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.1 h
      exact ⟨u, hu, by simpa using hm⟩
    · rintro ⟨u, hu, hm⟩
      exact ⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩
  have hMB : S.M d Λ ≤ B := le_inf hMA le_sup_right
  have hBA : B ≤ S.sat Λ := inf_le_left
  have hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ := Submodule.map_mono hBA
  haveI hfinB : Finite (B.map (S.M d Λ).mkQ) :=
    Finite.of_injective _ (Submodule.inclusion_injective hle')
  obtain ⟨i', hi'⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr
    (B.map (S.M d Λ).mkQ)).1
  have hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i' := hi'
  have hn : S.nLev d Λ J = S.q ^ i - S.q ^ i' := by
    rw [← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]
    unfold Frames.nLev
    congr 1
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, fun h => ?_, rfl⟩
      have := (hBmem y hy).1 h
      omega
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, ?_, rfl⟩
      have h1 := hle y hy
      have h2 : ¬ S.levC d Λ y ≤ J - 1 := fun h => hl ((hBmem y hy).2 h)
      omega
  have hlt : S.q ^ i' < S.q ^ i := by
    rw [← hcard, ← hi'q]
    obtain ⟨y, hy, hl⟩ := hPJ
    have hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂
        ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) := by
      refine ⟨hle', fun h => ?_⟩
      obtain ⟨b, hb, hby⟩ := h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)
      have h1 : b - y ∈ S.M d Λ := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y ∈ B := by
        have h3 : y = b - (b - y) := by abel
        rw [h3]
        exact B.sub_mem hb (hMB h1)
      have := (hBmem y hy).1 h2
      omega
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have hii : i' < i := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  exact ⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩

end GlobalTheory.HL.LevelFamilies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerFramesCoordinateLatticeGoodPlace
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdStab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_eq_one (hG : Good S) : S.th = 1 := by
  simp [Frames.th, hG.gg]

theorem image_all (g : Fin (r + 1) → S.V) :
    g '' {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.range g := by
  rw [show {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ from
    Set.eq_univ_of_forall fun i => i.is_lt, Set.image_univ]

theorem mem_span_iff (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (x : S.V) :
    x ∈ Submodule.span L.O (Set.range g) ↔ x ∈ S.stdLat g gs A ∧ x ∈ S.spanTo g (r + 1) := by
  rw [← image_all S g]
  exact ((GlobalTheory.HL.StdLat.stdLat_spec L r k S g gs hg A hA).2.1 (r + 1) le_rfl x).symm

theorem inv_apply_apply (h : S.GLV) (x : S.V) : h⁻¹ (h x) = x :=
  h.symm_apply_apply x

end

theorem stab_coordLat : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → S.a = 0 → ∀ d₀, S.IsTermW d₀ (coordLat S) 1 1 → S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG ha d₀ hT
  have hTerm : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hT⟩
  have hMeq := (GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ (coordLat S) 1 1 hT).2.1
  obtain ⟨hA, hA', -, -, hC1, hC2, -, -⟩ := hT
  rw [one_smul] at hC1 hC2
  have hf : ∀ x, x ∈ Submodule.span L.O (Set.range S.f) ↔
      x ∈ coordLat S ∧ x ∈ S.spanTo S.f (r + 1) := by
    intro x; rw [hC1]; exact mem_span_iff S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA x
  have hf' : ∀ x, x ∈ Submodule.span L.O (Set.range S.f') ↔
      x ∈ coordLat S ∧ x ∈ S.spanTo S.f' (r + 1) := by
    intro x; rw [hC2]; exact mem_span_iff S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA' x
  have th1 := th_eq_one S hG

  have key1 : ∀ h ∈ S.St, h • coordLat S = coordLat S → ∀ x,
      (x ∈ Submodule.span L.O (Set.range S.f) → h x ∈ Submodule.span L.O (Set.range S.f)) ∧
      (x ∈ Submodule.span L.O (Set.range S.f') → h x ∈ Submodule.span L.O (Set.range S.f')) := by
    intro h hh hC x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hf] at hx ⊢
      refine ⟨?_, (GlobalTheory.FrameAct.spanTo_iff S h hh _ x).2 hx.2⟩
      rw [← hC]; exact (GlobalTheory.FrameAct.mem_smul_iff S h _ x).2 hx.1
    · rw [hf'] at hx ⊢
      refine ⟨?_, (GlobalTheory.FrameAct.spanTo_iff' S h hh _ x).2 hx.2⟩
      rw [← hC]; exact (GlobalTheory.FrameAct.mem_smul_iff S h _ x).2 hx.1

  have key2 : ∀ g ∈ S.K0, ∀ x ∈ coordLat S, g x ∈ coordLat S := by
    intro g hg
    obtain ⟨⟨hgSt, hgf⟩, hgf'⟩ := hg
    replace hgf : g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := hgf
    replace hgf' : g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') := hgf'
    replace hgSt : g ∈ S.St := hgSt
    have gf : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) →
        ∀ b, g (S.f b) ∈ coordLat S := by
      intro g hg b
      have h1 : g (S.f b) ∈ Submodule.span L.O (Set.range S.f) := by
        rw [← hg]; exact (GlobalTheory.FrameAct.mem_smul_iff S g _ _).2 (Submodule.subset_span ⟨b, rfl⟩)
      exact ((hf _).1 h1).1
    have gf' : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') →
        ∀ b, g (S.f' b) ∈ coordLat S := by
      intro g hg b
      have h1 : g (S.f' b) ∈ Submodule.span L.O (Set.range S.f') := by
        rw [← hg]; exact (GlobalTheory.FrameAct.mem_smul_iff S g _ _).2 (Submodule.subset_span ⟨b, rfl⟩)
      exact ((hf' _).1 h1).1
    have hM : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) →
        g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') →
        ∀ m ∈ S.Mof S.f S.f', g m ∈ coordLat S := by
      intro g h1 h2 m hm
      induction hm using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact gf g h1 b
        · simp only [th1, inv_one, map_one, one_smul, map_sub]
          exact (coordLat S).sub_mem (gf' g h2 b) (gf g h1 b)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact (coordLat S).add_mem hx hy
      | smul c x _ hx =>
        have e : g (c • x) = c • g x := by
          first
            | exact LinearEquiv.map_smul_of_tower g c x
            | exact g.toLinearMap.map_smul_of_tower c x
            | (rw [Subring.smul_def, map_smul, ← Subring.smul_def])
        rw [e]; exact (coordLat S).smul_mem c hx
    intro x hx
    obtain ⟨-, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
    have hx' : x ∈ S.ME ⊔ S.W0 := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    have hmM : m ∈ S.Mof S.f S.f' := by
      have := GlobalTheory.HL.UnimodTerm.proj_mem S hTerm ha hx hm (by simpa using hw)
      rw [hMeq] at this; exact this
    have hw' : w ∈ coordLat S := by
      have h1 := hM 1 (one_smul _ _) (one_smul _ _) m hmM
      have : w = (m + w) - m := by abel
      rw [this]; exact (coordLat S).sub_mem hx h1
    rw [map_add, (GlobalTheory.HL.FrameStab.stab_eq L r k S).1 g hgSt w hw]
    exact (coordLat S).add_mem (hM g hgf hgf' m hmM) hw'
  ext h
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Frames.K0]
  constructor
  · rintro ⟨hh, hC⟩
    have hC' : h⁻¹ • coordLat S = coordLat S := by rw [inv_smul_eq_iff]; exact hC.symm
    have hhi : h⁻¹ ∈ S.St := inv_mem hh
    refine ⟨⟨hh, ?_⟩, ?_⟩
    · refine (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, (key1 h hh hC x).1⟩).symm
      have := (key1 h⁻¹ hhi hC' (h x)).1 hx
      rwa [inv_apply_apply] at this
    · refine (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, (key1 h hh hC x).2⟩).symm
      have := (key1 h⁻¹ hhi hC' (h x)).2 hx
      rwa [inv_apply_apply] at this
  · rintro ⟨⟨hh, h1⟩, h2⟩
    have hK : h ∈ S.K0 := ⟨⟨hh, h1⟩, h2⟩
    refine ⟨hh, (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, key2 h hK x⟩).symm⟩
    have := key2 h⁻¹ (inv_mem hK) _ hx
    rwa [inv_apply_apply] at this

end GlobalTheory.HL.StdStab
end

