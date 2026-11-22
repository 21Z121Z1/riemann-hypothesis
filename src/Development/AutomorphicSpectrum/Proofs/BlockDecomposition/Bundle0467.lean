import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationEqConjNilpotentIntegral
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IwJac.FiltTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_one_of_ord {ϖ : kˣ} (h : ord k ϖ = 1) : valuation k (ϖ : k) ≤ 1 := by
  have h' : -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (ϖ : k))) = 1 := h
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (ϖ : k)) ≠ 0 := by simp
  have h1 : WithZero.log (φ (valuation k (ϖ : k))) = -1 := by omega
  rw [← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, h1, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem tor_neg (ϖ : kˣ) (x : Fin n → ℤ) : tor ϖ (-x) = (tor ϖ x)⁻¹ := by
  unfold tor; rw [← map_inv]; congr 1; funext i; simp [_root_.zpow_neg]

theorem conj_tor_apply (ϖ : kˣ) (y : Fin n → ℤ) (m : GL (Fin n) k) (i j : Fin n) :
    ((MulAut.conj (tor ϖ y) m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (y i - y j) : kˣ) : k) * (m : Matrix (Fin n) (Fin n) k) i j := by
  rw [MulAut.conj_apply, ← tor_neg, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, mul_diagonal, diagonal_mul, _root_.zpow_sub]
  simp only [Pi.neg_apply, _root_.zpow_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem int_of_mem_KO {m : GL (Fin n) k} (h : m ∈ GlobalTheory.SplitWeil.KO k (Fin n)) (i j : Fin n) :
    valuation k ((m : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨u, rfl⟩ := h
  exact (u.val i j).2

theorem mem_KO_of_int {g : GL (Fin n) k}
    (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    g ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_nO_of {g : GL (Fin n) k} (hg : g ∈ unipB k (Fin n))
    (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    g ∈ nO k n := by
  refine ⟨mem_iwahori.2 ⟨mem_KO_of_int h1 h2, fun i j hji => ?_⟩, hg⟩
  rw [((mem_unipB k).1 hg).1 i j hji, map_zero]
  exact zero_lt_one

theorem conj_mem_nO {ϖ : kˣ} {y : Fin n → ℤ} {m : GL (Fin n) k} (hm : m ∈ unipB k (Fin n))
    (h1 : ∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * (m : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    MulAut.conj (tor ϖ y) m ∈ nO k n := by
  have hu : ∀ m' ∈ unipB k (Fin n), (∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * (m' : Matrix (Fin n) (Fin n) k) i j) ≤ 1) →
      MulAut.conj (tor ϖ y) m' ∈ unipB k (Fin n) ∧
        ∀ i j, valuation k (((MulAut.conj (tor ϖ y) m' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro m' hm' h
    obtain ⟨h0, hd⟩ := (mem_unipB k).1 hm'
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i j => ?_⟩
    · rw [conj_tor_apply, h0 i j hji, mul_zero]
    · rw [conj_tor_apply, hd, sub_self, zpow_zero, Units.val_one, mul_one]
    · rw [conj_tor_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact h i j hij
      · rw [hd, sub_self, zpow_zero, Units.val_one, mul_one, map_one]
      · rw [h0 i j hij, mul_zero, map_zero]; exact zero_le'
  obtain ⟨a1, a2⟩ := hu m hm h1
  obtain ⟨_, b2⟩ := hu m⁻¹ (inv_mem hm) h2
  exact mem_nO_of a1 a2 (by rw [← map_inv]; exact b2)

theorem filt_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : ord k ϖ = 1) (x : Fin n → ℤ) (hx : StrictAnti x) :
    filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom := by
  have hv := val_le_one_of_ord hϖ
  have pint : ∀ i j : Fin n, i < j → valuation k ((ϖ ^ (x i - x j) : kˣ) : k) ≤ 1 := by
    intro i j hij
    obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (hx hij).le)
    rw [he, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one₀ zero_le' hv
  have cancel : ∀ i j : Fin n, valuation k ((ϖ ^ ((-x) i - (-x) j) : kˣ) : k) *
      valuation k ((ϖ ^ (x i - x j) : kˣ) : k) = 1 := by
    intro i j
    rw [← map_mul, ← Units.val_mul, ← _root_.zpow_add,
      show (-x) i - (-x) j + (x i - x j) = 0 by simp only [Pi.neg_apply]; ring,
      zpow_zero, Units.val_one, map_one]
  ext g
  rw [Subgroup.mem_map, mem_filt]
  constructor
  · rintro ⟨hg, dg, dg'⟩
    refine ⟨MulAut.conj (tor ϖ (-x)) g, conj_mem_nO hg.2 (fun i j hij => ?_) (fun i j hij => ?_), ?_⟩
    · rw [map_mul, ← cancel i j]
      exact mul_le_mul_right (dg i j hij (by have := j.isLt; omega)) _
    · rw [map_mul, ← cancel i j]
      exact mul_le_mul_right (dg' i j hij (by have := j.isLt; omega)) _
    · show MulAut.conj (tor ϖ x) (MulAut.conj (tor ϖ (-x)) g) = g
      rw [tor_neg]
      simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨m, hm, rfl⟩
    show MulAut.conj (tor ϖ x) m ∈ nO k n ∧ Deep ϖ x n (MulAut.conj (tor ϖ x) m) ∧
      Deep ϖ x n (MulAut.conj (tor ϖ x) m)⁻¹
    have key : ∀ m' ∈ nO k n, ∀ i j : Fin n,
        valuation k (((ϖ ^ (x i - x j) : kˣ) : k) * (m' : Matrix (Fin n) (Fin n) k) i j) ≤
          valuation k ((ϖ ^ (x i - x j) : kˣ) : k) := by
      intro m' hm' i j
      rw [map_mul]
      exact mul_le_of_le_one_right' (int_of_mem_KO (iwahori_le_KO k (Fin n) hm'.1) i j)
    have hm' := inv_mem hm
    refine ⟨conj_mem_nO hm.2 (fun i j hij => (key m hm i j).trans (pint i j hij))
      (fun i j hij => (key _ hm' i j).trans (pint i j hij)), fun i j _ _ => ?_, fun i j _ _ => ?_⟩
    · rw [conj_tor_apply]; exact key m hm i j
    · rw [← map_inv, conj_tor_apply]; exact key _ hm' i j

theorem filt_top' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
      filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom :=
  fun k _ _ _ _ n ϖ hϖ x hx => filt_top k n ϖ hϖ x hx

end GlobalTheory.CompanionTheory.IwJac.FiltTop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFibreFunctionsCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibFin

theorem finite_image_of_rightInvariant {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) (hS : IsOpen (S : Set G)) {K : Set G} (hK : IsCompact K) (F : G → X)
    (hF : ∀ g, ∀ s ∈ S, F (g * s) = F g) : (F '' K).Finite := by
  have hcover : K ⊆ ⋃ g : K, (fun x => (g : G) * x) '' (S : Set G) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, 1, S.one_mem, mul_one x⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun g : K => (fun x => (g : G) * x) '' (S : Set G))
    (fun g => (Homeomorph.mulLeft (g : G)).isOpenMap _ hS) hcover
  apply (T.finite_toSet.image (fun g : K => F g)).subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (hT hx)
  obtain ⟨s, hs, rfl⟩ := hxg
  exact ⟨g, hg, (hF g s hs).symm⟩

theorem finite_fibV_image (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    ((fun κ : GL (Fin (i + t)) k => fibV f κ) ''
      (GlobalTheory.SplitWeil.KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite := by
  have hst : IsOpen {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} :=
    GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd (GlobalTheory.BZMir.Leib.HPG k i t)
      (GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ) f
  let H : Subgroup (GL (Fin (i + t)) k) :=
    { carrier := {g | ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * g) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ}
      mul_mem' := by
        intro a b ha hb κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        have hb' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * b) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := hb
        rw [← mul_assoc, hb', ha']
      one_mem' := by
        intro κ
        rw [mul_one]
      inv_mem' := by
        intro a ha κ
        have ha' : ∀ κ, GlobalTheory.CompanionTheory.BZPsiPG.fibV f (κ * a) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f κ := ha
        rw [← ha' (κ * a⁻¹), mul_assoc, inv_mul_cancel, mul_one] }
  have hcont := (GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k (i + t)).1
  have hO := hcont.isOpen_preimage _ hst
  have hone : (1 : GL (Fin (i + t)) k) ∈ GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} := by
    show GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) 1) f = f
    simp
  have hsub : GlobalTheory.BZMir.levi k (i + t) ⁻¹'
      {m : GlobalTheory.BZMir.Mir k (i + t) | GlobalTheory.BZMir.Leib.prodPG τ σ m f = f} ⊆ (H : Set _) := by
    intro g hg κ
    have hg' : GlobalTheory.BZMir.Leib.prodPG τ σ (GlobalTheory.BZMir.levi k (i + t) g) f = f := hg
    funext v
    have h1 := congrArg (fun φ => GlobalTheory.CompanionTheory.BZPsiPG.fibV φ κ v) hg'
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.fibV, map_mul, ← mul_assoc] at h1 ⊢
    exact h1
  have hHopen : IsOpen (H : Set (GL (Fin (i + t)) k)) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds hone) hsub)
  have hF : ∀ g : GL (Fin (i + t)) k, ∀ s ∈ H,
      GlobalTheory.CompanionTheory.BZPsiPG.fibV f (g * s) = GlobalTheory.CompanionTheory.BZPsiPG.fibV f g := fun g s hs => hs g
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibFin.finite_image_of_rightInvariant H hHopen GlobalTheory.SplitFlip.isCompact_KO _ hF

end GlobalTheory.CompanionTheory.BZPsiPG.FibFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintLevel

theorem finsum_out_of_le {H : Type} [Group H] {L S : Subgroup H} (u : H → ℂ) (hLS : L ≤ S)
    (hS : S ≤ rStab u) (hm : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ c : H ⧸ S, u c.out := by
  have hm' : Nat.card (S ⧸ L.subgroupOf S) ≠ 0 := hm
  haveI : Finite (S ⧸ L.subgroupOf S) := Nat.finite_of_card_ne_zero hm'
  let e := Subgroup.quotientEquivProdOfLE hLS
  have hfst : ∀ q : H ⧸ L, (e q).1 = ((q.out : H) : H ⧸ S) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (e (g : H ⧸ L)).1 = (g : H ⧸ S) := rfl
    rw [h1]
    exact QuotientGroup.eq.2 (hLS (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : H ⧸ L)).symm))
  have hg : ∀ q : H ⧸ L, u q.out = u (e q).1.out := by
    intro q
    rw [hfst q]
    have hk : (((q.out : H) : H ⧸ S).out)⁻¹ * q.out ∈ S :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' ((q.out : H) : H ⧸ S))
    have := hS hk (((q.out : H) : H ⧸ S).out)
    simpa using this
  have hcomp : ∑ᶠ q : H ⧸ L, u q.out =
      ∑ᶠ p : (H ⧸ S) × (S ⧸ L.subgroupOf S), u p.1.out := by
    rw [← finsum_comp_equiv e]
    exact finsum_congr hg
  rw [hcomp]
  by_cases hfin : (Function.support fun c : H ⧸ S => u c.out).Finite
  · have hsupp : (Function.support fun p : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u p.1.out).Finite := by
      refine (hfin.prod (Set.finite_univ (α := S ⧸ L.subgroupOf S))).subset ?_
      intro p hp
      exact ⟨hp, Set.mem_univ _⟩
    rw [finsum_curry _ hsupp]
    have hin : ∀ c : H ⧸ S, ∑ᶠ _ : S ⧸ L.subgroupOf S, u c.out = ((L.relIndex S : ℕ) : ℂ) * u c.out := by
      intro c
      haveI := Fintype.ofFinite (S ⧸ L.subgroupOf S)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rfl
    simp only [hin]
    rw [mul_finsum]
  · have h0 : ∑ᶠ c : H ⧸ S, u c.out = 0 := finsum_of_infinite_support hfin
    rw [h0, mul_zero]
    refine finsum_of_infinite_support fun hsupp => hfin ?_
    refine (hsupp.image Prod.fst).subset ?_
    intro c hc
    exact ⟨(c, ((1 : S) : S ⧸ L.subgroupOf S)), hc, rfl⟩

theorem hint_eq_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hfin
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have hm : L.relIndex (rStab u ⊓ K) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  rw [finsum_out_of_le u hLS inf_le_left hm, ← hmul, hint]
  have hmC : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [Nat.cast_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.HintLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.EisTerm

theorem flat_norm_le_height_rpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y))
    (a : G2 σ Y → ℝ) (hK : IsCompact (K : Set (G2 σ Y))) (hH : IsHgt K a) (ha : ∀ x, 0 < a x)
    (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun s x => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hH.iwa x
  have hpos := ha (p * k)
  have hval := hH.val p t hp k hk
  have hlaw := hf.law p t k hp
  have hfk : ‖f (p * k)‖ = a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖ := by
    have h1 : ‖(χ (Matrix.GeneralLinearGroup.det t) : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
        | exact mem_sphere_zero_iff_norm.mp (χ (Matrix.GeneralLinearGroup.det t)).2
    rw [hlaw, ← hval, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, h1, one_mul]
    congr 2
    simp
  have e1 : a (p * k) ^ (s.re + (n : ℝ) / 2) =
      a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add hpos]
    congr 1
    rw [Complex.sub_re]
    ring
  show ‖((a (p * k) : ℝ) : ℂ) ^ (s - s₁) * f (p * k)‖ ≤ _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hfk, e1]
  have h0 : 0 ≤ a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hpos.le _)
  calc a (p * k) ^ ((s - s₁).re) * (a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖)
      = (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * ‖f k‖ := by ring
    _ ≤ (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * C :=
      mul_le_mul_of_nonneg_left (hC k hk) h0
    _ = C * (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) := by ring

end GlobalTheory.CompanionTheory.EisTerm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlipUSymmCont
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.CompanionTheory.NegDS

variable {n : ℕ} {ε ε' : Fin n → Bool}

theorem sign_eq_iff (he : ∀ a, ε' a = !ε a) (a b : Fin n) : ε' a = ε' b ↔ ε a = ε b := by
  rw [he a, he b]
  cases ε a <;> cases ε b <;> simp

theorem Jm_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Jm ε' = -Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_neg]
  congr 1
  funext a
  rw [he a]
  cases ε a <;> simp

theorem UJset_flip (he : ∀ a, ε' a = !ε a) : Formalism.MainNotions.S.UJset ε' = Formalism.MainNotions.S.UJset ε := by
  ext g
  show Formalism.REAL.inUJ ε' g ↔ Formalism.REAL.inUJ ε g
  unfold Formalism.REAL.inUJ
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem Kset_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Kset ε' = Formalism.REAL.Kset ε := by
  ext g
  show g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε' = Formalism.REAL.Jm ε' * g ↔
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoC ε' = Formalism.REAL.rhoC ε := by
  funext a
  simp only [Formalism.REAL.rhoC, sign_eq_iff he]

theorem rhoN_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoN ε' = Formalism.REAL.rhoN ε := by
  funext a
  simp only [Formalism.REAL.rhoN, ne_eq, sign_eq_iff he]

theorem lowK_flip (he : ∀ a, ε' a = !ε a) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK ε' lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK
  rw [rhoC_flip he, rhoN_flip he]

theorem vNormSq_flip (he : ∀ a, ε' a = !ε a) (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq ε' μ = Formalism.MainNotions.S.vNormSq ε μ := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [rhoC_flip he]

theorem cdom_flip (he : ∀ a, ε' a = !ε a) (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom ε' μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp only [Formalism.MainNotions.S.CDom, sign_eq_iff he]

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kstable_flip (he : ∀ a, ε' a = !ε a) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKStableOn ε' σ S ↔ Formalism.MainNotions.S.IsKStableOn ε σ S := by
  simp only [Formalism.MainNotions.S.IsKStableOn, Kset_flip he]

theorem ktype_flip (he : ∀ a, ε' a = !ε a) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε' σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, kstable_flip he, Kset_flip he, cdom_flip he]

end Rep

def flipU (he : ∀ a, ε' a = !ε a) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).1 g.2⟩
  invFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem flipU_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he) := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem flipU_symm_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he).symm := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem memLp_flip (he : ∀ a, ε' a = !ε a) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU he) 2 (Formalism.REAL.muG ε') := by
  have hc := flipU_cont he
  have hcs := flipU_symm_cont he
  let eH : Formalism.REAL.UJ ε' ≃ₜ Formalism.REAL.UJ ε := ⟨(flipU he).toEquiv, hc, hcs⟩
  have hme : MeasurableEmbedding (flipU he) := eH.measurableEmbedding
  haveI : (Measure.map (flipU he) (Formalism.REAL.muG ε')).IsHaarMeasure :=
    (flipU he).isHaarMeasure_map (Formalism.REAL.muG ε') hc hcs
  have hmap : Measure.map (flipU he) (Formalism.REAL.muG ε') =
      MeasureTheory.Measure.haarScalarFactor (Measure.map (flipU he) (Formalism.REAL.muG ε')) (Formalism.REAL.muG ε) •
        Formalism.REAL.muG ε :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  rw [← hme.memLp_map_measure_iff, hmap, ENNReal.smul_def]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem sqInt_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : ∀ a, ε' a = !ε a) (h : Formalism.MainNotions.S.IsSqIntOn ε σ) : Formalism.MainNotions.S.IsSqIntOn ε' σ := by
  intro v w
  have e : Formalism.MainNotions.S.coefOn (ε := ε') σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU he := by
    funext g
    rfl
  rw [e]
  exact memLp_flip he (h v w)

theorem isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ h
  have he : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl
  unfold Formalism.MainNotions.S.IsDS at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, sqInt_flip he h5, ?_, ?_⟩
  · rw [UJset_flip he]
    exact h3
  · rw [UJset_flip he]
    exact h4
  · obtain ⟨S, hS⟩ := h6
    exact ⟨S, by rw [lowK_flip he, ktype_flip he]; exact hS⟩
  · intro μ S hS
    rw [lowK_flip he, vNormSq_flip he, vNormSq_flip he]
    exact h7 μ S ((ktype_flip he μ S).1 hS)

end GlobalTheory.CompanionTheory.NegDS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUniqueStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_artin_map_unique : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | exact GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | (intros; apply GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureOpenNonemptyNeZero
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem muD_toReal_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    ((muD k t) E).toReal ≠ 0 := by
  intro k _ _ _ _ t E C hE hn hC hEC
  unfold muD
  rw [ENNReal.toReal_ne_zero]
  exact ⟨(hE.measure_pos _ hn).ne',
    ((MeasureTheory.measure_mono hEC).trans_lt hC.measure_lt_top).ne⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

