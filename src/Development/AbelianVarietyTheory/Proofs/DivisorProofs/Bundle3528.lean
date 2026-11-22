import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModuliOfSignatureEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenselia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSucc
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def extend (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) (V : (Fin (m + 1) → HermLB p) → X → ℝ) :
    ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ :=
  fun d L x => if h : d = m + 1 then V (fun a => L (Fin.cast h.symm a)) x else T d L x

theorem extend_of_ne {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    {d : ℕ} (h : d ≠ m + 1) (L : Fin d → HermLB p) (x : X) : extend m T V d L x = T d L x := dif_neg h

theorem extend_self {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    (L : Fin (m + 1) → HermLB p) (x : X) : extend m T V (m + 1) L x = V L x := by
  simp [extend]

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ} {h h' : Y → ℝ}
    (H : ∀ z, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem isRatSec_tens_mul {Z : Scheme.{0}} [IsIntegral Z] {A B : LB Z} {r : A.ι → Z.functionFieldˣ}
    {s : B.ι → Z.functionFieldˣ} (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem isMix_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  intro hI hR m hm k _ X p hp
  classical
  haveI : IsNoetherian X := hp.isNoetherian
  obtain ⟨T, hT⟩ := hm k X p hp
  choose v hv using GlobalTheory.T.mixedHeightRecursiveValue_well_defined hI hR m hm k X p hp T hT
  have hD := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have hdimi : ∀ (Y : Scheme.{0}) [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ),
      topologicalKrullDim Y = (d : ℕ) → HasDim (i (genericPoint Y)) d := fun Y _ i _ d h =>
    (hD.2.2.2.2.1 Y i (genericPoint Y) d).2 ((hD.2.2.2.2.2 Y d).2 h)
  have hcd : ∀ x : X, HasDim x (m + 1) → topologicalKrullDim (clo x) = ((m + 1 : ℕ) : WithBot ℕ∞) := fun x hx =>
    (hD.2.2.2.2.2 (clo x) (m + 1)).1
      ((hD.2.2.2.2.1 (clo x) (cloι x) (genericPoint (clo x)) (m + 1)).1 (by rw [cloι_genericPoint]; exact hx))
  have E : ∀ (x : X) (hx : HasDim x (m + 1)) (M : HermLB p) (L : Fin m → HermLB p)
      (M' : HermLB (cloι x ≫ p)) (L' : Fin m → HermLB (cloι x ≫ p)),
      (M.pull (cloι x) rfl).Isometric M' → (∀ a, ((L a).pull (cloι x) rfl).Isometric (L' a)) →
      ∀ (r : M'.B.ι → (clo x).functionFieldˣ) (hr : IsRatSec M'.B r)
        (TY : ∀ d : ℕ, (Fin d → HermLB (cloι x ≫ p)) → clo x → ℝ), IsMix (cloι x ≫ p) m TY →
      v x hx M L = recVal (TY m L') L' M' hr := by
    intro x hx M L M' L' hM hL r hr TY hTY
    rw [hv x hx M L (clo x) (cloι x ≫ p) (cloι x) rfl (cloι_genericPoint x) M' L' hM hL r hr]
    refine recVal_congr (fun z hz => ?_) L' M' hr
    have hz' : HasDim z m := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo x) (cloι x ≫ p) (hp.sub _) m (hcd x hx)).1 z).1 hz
    exact GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X (clo x) p (cloι x ≫ p) hp (cloι x) rfl m m T TY hT hTY m le_rfl le_rfl L L' hL z hz'
  let V : (Fin (m + 1) → HermLB p) → X → ℝ := fun L x =>
    if hx : HasDim x (m + 1) then v x hx (L 0) (Fin.tail L) else 0
  have hV : ∀ (L : Fin (m + 1) → HermLB p) (x : X) (hx : HasDim x (m + 1)),
      extend m T V (m + 1) L x = v x hx (L 0) (Fin.tail L) := fun L x hx => by
    rw [extend_self]
    exact dif_pos hx
  have hsym : ∀ (x : X) (hx : HasDim x (m + 1)) (L : Fin (m + 1) → HermLB p) (e : Equiv.Perm (Fin (m + 1))),
      v x hx (L (e 0)) (Fin.tail fun a => L (e a)) = v x hx (L 0) (Fin.tail L) := by
    intro x hx L e
    obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
    have hq : IsAmb (cloι x ≫ p) := hp.sub (cloι x)
    have hdx := hcd x hx
    let F : (Fin (m + 1) → HermLB p) → ℝ := fun L => v x hx (L 0) (Fin.tail L)
    change F (fun a => L (e a)) = F L
    rcases m with _ | n
    · have : (fun a => L (e a)) = L := funext fun a => congrArg L (@Subsingleton.elim (Fin 1) _ _ _)
      rw [this]
    · refine GlobalTheory.T.perm_invariant_of_cons_swap_and_tail (HermLB p) n F (fun a L τ => ?_) (fun a b L => ?_) L e
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        rw [E x hx a (fun i => L (τ i)) (a.pull (cloι x) rfl) (fun i => (L (τ i)).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
          E x hx a L (a.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY]
        exact (GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hI k (clo x) (cloι x ≫ p) hq (n + 1) hdx TY hTY _ ra hra).2.1
          (fun i => (L i).pull (cloι x) rfl) τ
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (b.pull (cloι x) rfl).isLB
        have iso : ∀ (c : HermLB p) (j : Fin (n + 1)), ((Fin.cons c L : Fin (n + 1) → HermLB p) j).pull (cloι x) rfl |>.Isometric
            ((Fin.cons (c.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl) : Fin (n + 1) → HermLB (cloι x ≫ p)) j) := by
          intro c j
          refine Fin.cases ?_ (fun i => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> exact HermLB.Isometric.refl _
        rw [E x hx a _ (a.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso b) ra hra TY hTY,
          E x hx b _ (b.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso a) rb hrb TY hTY]
        exact GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo hI hR k (clo x) (cloι x ≫ p) hq n hdx TY hTY _ _ _ ra hra rb hrb
  refine ⟨extend m T V, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d L M x hd hx hLM
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨r, hr⟩ := Cartier.exists_isRatSec ((L 0).pull (cloι x) rfl).isLB
      rw [E x hx (L 0) (Fin.tail L) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr TY hTY,
        E x hx (M 0) (Fin.tail M) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          ((hLM 0).symm.pull _ _) (fun a => (hLM a.succ).symm.pull _ _) r hr TY hTY]
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.iso d L M x (by omega) hx hLM
  · intro d L e x hd hx
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      exact hsym x hx L e
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.symm d L e x (by omega) hx
  · intro d A B L x hd hx
    by_cases h : d + 1 = m + 1
    · obtain rfl : d = m := by omega
      rw [hV _ _ hx, hV _ _ hx, hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (A.pull (cloι x) rfl).isLB
      obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (B.pull (cloι x) rfl).isLB
      have ht := isRatSec_tens_mul hra hrb
      rw [E x hx (A.tens B) L ((A.pull (cloι x) rfl).tens (B.pull (cloι x) rfl)) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.isometric_pull_tens A B _ _) (fun _ => HermLB.Isometric.refl _) _ ht TY hTY,
        E x hx A L (A.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
        E x hx B L (B.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) rb hrb TY hTY]
      exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k (clo x) (cloι x ≫ p) (hp.sub _) d (hcd x hx) _ _ _ _ ra hra rb hrb _ ht
        fun _ _ _ _ => rfl
    · rw [extend_of_ne h, extend_of_ne h, extend_of_ne h]
      exact hT.add d A B L x (by omega) hx
  · intro L x hx
    rw [extend_of_ne (by omega)]
    exact hT.zero L x hx
  · intro Y _ _ q i _ hi e he hdim M L M' L' hM hL r hr
    have hfun : (fun z => extend m T V e L (i z)) = fun z => T e L (i z) :=
      funext fun z => extend_of_ne (by omega) L (i z)
    rw [hfun]
    by_cases h : e + 1 = m + 1
    · obtain rfl : e = m := by omega
      have hx := hdimi Y i (e + 1) hdim
      rw [hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact hv _ hx M L Y q i hi rfl M' L' hM hL r hr
    · rw [extend_of_ne h]
      exact hT.recur Y q i hi e (by omega) hdim M L M' L' hM hL r hr

end GlobalTheory.MixHt.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicImageNotOntoModConjIdeal
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.CoisBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cois_dvd (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) {n : ℕ} (hn : 0 < n) (hc : Cois D y n) {p : ℕ} (hpn : p ∣ n) (a : D.La)
    (ha : ∀ b, (∃ e, y b = p • e) → (p : ℤ) ∣ D.EF a b) : ∃ e, y a = p • e := by
  obtain ⟨k, rfl⟩ := hpn
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨e, he⟩ := hc.2 (k • a) fun b ⟨e, he⟩ => by
    obtain ⟨c, hc'⟩ := ha b ⟨k • e, by rw [he, mul_smul]⟩
    exact ⟨c, by rw [map_nsmul, LinearMap.smul_apply, hc', nsmul_eq_mul]; push_cast; ring⟩
  refine ⟨e, ?_⟩
  have h2 : (k : ℤ) • (y a - p • e) = 0 := by
    rw [natCast_zsmul, smul_sub, ← map_nsmul, he, smul_smul, mul_comm k p, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (by exact_mod_cast h) hk
  · exact sub_eq_zero.1 h

theorem exists_pair (D : Datum H) {p : ℕ} (hp : p.Prime) (S : AddSubgroup D.La) (hpS : ∀ x : D.La, p • x ∈ S)
    {c : D.La} (hc : c ∉ S) : ∃ a : D.La, (∀ b ∈ S, (p : ℤ) ∣ D.EF a b) ∧ ¬ (p : ℤ) ∣ D.EF a c := by
  haveI := Fact.mk hp
  letI : Module (ZMod p) (D.La ⧸ S) := AddCommGroup.zmodModule (fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H x => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact hpS x)
  have hc' : (QuotientAddGroup.mk c : D.La ⧸ S) ≠ 0 := by rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨f, hf⟩ : ∃ f : (D.La ⧸ S) →+ ZMod p, f (QuotientAddGroup.mk c) ≠ 0 := by
    by_contra hne
    push_neg at hne
    refine hc' ((Module.forall_dual_apply_eq_zero_iff (ZMod p) _).1 fun φ => ?_)
    exact hne (LinearMap.toAddMonoidHom φ)
  let g : D.La →+ ZMod p := f.comp (QuotientAddGroup.mk' S)
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let bs := Module.Free.chooseBasis ℤ D.La
  let G : D.La →ₗ[ℤ] ℤ := bs.constr ℤ (fun i => ((g (bs i)).val : ℤ))
  have hG : ∀ x, ((G x : ℤ) : ZMod p) = g x := by
    have : (Int.castAddHom (ZMod p)).toIntLinearMap.comp G = g.toIntLinearMap := bs.ext fun i => by
      simp [G, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun this x
  obtain ⟨a, ha⟩ := D.unimod.2 G
  refine ⟨a, fun b hb => ?_, fun hdvd => hf ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ha, hG]
    show f (QuotientAddGroup.mk b) = 0
    rw [(QuotientAddGroup.eq_zero_iff b).2 hb, map_zero]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ha, hG] at hdvd
    exact hdvd

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem mem_nsmul_of_dvd (h : IsOpp D Z Z') {p : ℕ} (hp : 0 < p) {z : D.La} (hz : z ∈ Z)
    (hd : ∀ b ∈ Z', (p : ℤ) ∣ D.EF z b) : ∃ w ∈ Z, z = p • w := by
  choose c hc using fun b : Z' => hd b b.2
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  let φ : Z' →+ ℤ := AddMonoidHom.mk' c fun x x' =>
    mul_left_cancel₀ hp' (by rw [mul_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add])
  obtain ⟨w, hw, -⟩ := h.2.2.2 φ
  refine ⟨w, w.2, ?_⟩
  have : z - p • (w : D.La) = 0 := h.symm.eq_zero (sub_mem hz (Z.nsmul_mem w.2 p)) fun b hb => by
    have := hw ⟨b, hb⟩
    simp only [AddMonoidHom.mk'_apply, φ] at this
    rw [map_sub, LinearMap.sub_apply, map_nsmul, LinearMap.smul_apply, this, hc ⟨b, hb⟩, nsmul_eq_mul, sub_self]
  exact sub_eq_zero.1 this

end GlobalTheory.LowFilt.CoisBar

namespace GlobalTheory.LowFilt.CoisBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_nsmul_of_img_eq_top (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔮 : Ideal (𝓞 E)) (h𝔮 : 𝔮.IsMaximal)
    (htop : img D y Z' 𝔮 = ⊤) {p : ℕ} {b : D.La} (hb : b ∈ Z') (hyb : ∃ e, y b = p • e)
    (hq : ∀ t ∈ 𝔮, ∃ e ∈ Z', t • b = p • e) : ∃ e ∈ Z', b = p • e := by
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨r, hr1, hrX⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := 𝔮) (N := Z'.map y)
    (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl (le_of_eq htop.symm)
  have hr0 : r ∉ 𝔮 := fun h' => h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' hr1))
  have hrx : ∀ x : X, ∃ k ∈ Z', y k = r • x := fun x =>
    Submodule.mem_map.1 (hrX (Submodule.smul_mem_pointwise_smul x r ⊤ trivial))
  have hinj : ∀ k ∈ Z', y k = 0 → k = 0 := by
    obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
    have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
      obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
      rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
        GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
    have hr00 : r ≠ 0 := fun h0 => hr0 (h0 ▸ 𝔮.zero_mem)
    set N := Ideal.absNorm (Ideal.span {r}) with hN
    have hN0 : N ≠ 0 := by
      rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr00
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    let g : Z' →ₗ[ℤ] X := (y.restrictScalars ℤ).comp (Z'.subtype.restrictScalars ℤ)
    have hmem : ∀ x : X, (N • LinearMap.id : X →ₗ[ℤ] X) x ∈ LinearMap.range g := fun x => by
      obtain ⟨k, hk, hyk⟩ := hrx (s • x)
      refine ⟨⟨k, hk⟩, ?_⟩
      show y k = N • x
      rw [hyk, smul_smul, mul_comm, hs, Nat.cast_smul_eq_nsmul]
    let m : X →ₗ[ℤ] LinearMap.range g := LinearMap.codRestrict _ (N • LinearMap.id) hmem
    have hm : Function.Injective m := fun x x' hxx => by
      have h1 : (N : ℤ) • (x - x') = 0 := by
        have : N • x = N • x' := congrArg Subtype.val hxx
        rw [natCast_zsmul, smul_sub, this, sub_self]
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd (by exact_mod_cast h2) hN0
      · exact sub_eq_zero.1 h2
    have h1 := LinearMap.rank_le_of_injective m hm
    have h2 := LinearMap.rank_range_add_rank_ker g
    have h3 := rank_range_le g
    rw [← Module.finrank_eq_rank (R := ℤ) (M := X)] at h1
    rw [← Module.finrank_eq_rank (R := ℤ) (M := Z'), hrank] at h2 h3
    have h4 : Module.rank ℤ (LinearMap.range g) = Module.finrank ℤ X := le_antisymm h3 h1
    rw [h4] at h2
    have h5 : Module.rank ℤ (LinearMap.ker g) = 0 := by
      obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt (le_add_self.trans h2.le) (Cardinal.nat_lt_aleph0 _))
      rw [hk] at h2 ⊢
      norm_cast at h2 ⊢
      omega
    intro k hk hyk
    obtain ⟨a, ha0, hak⟩ := (rank_eq_zero_iff.1 h5) ⟨⟨k, hk⟩, hyk⟩
    have : a • (⟨k, hk⟩ : Z') = 0 := congrArg Subtype.val hak
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' ha0
    · exact congrArg Subtype.val h'
  obtain ⟨x, hx⟩ := hyb
  obtain ⟨b'', hb'', hyb''⟩ := hrx x
  have hrb : r • b = p • b'' := sub_eq_zero.1 (hinj _ (sub_mem (Z'.smul_mem r hb) (Z'.nsmul_mem hb'' p))
    (by rw [map_sub, map_smul, map_nsmul, hx, hyb'', smul_comm r p x, sub_self]))
  obtain ⟨c, u, hu, hcu⟩ := h𝔮.exists_inv hr0
  obtain ⟨e, he, hue⟩ := hq u hu
  refine ⟨c • b'' + e, add_mem (Z'.smul_mem c hb'') he, ?_⟩
  calc b = (c * r + u) • b := by rw [hcu, one_smul]
    _ = p • (c • b'' + e) := by rw [add_smul, mul_smul, hrb, hue, smul_add, smul_comm c p]

end GlobalTheory.LowFilt.CoisBar

namespace GlobalTheory.LowFilt.CoisBar

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL htop
  obtain ⟨p, hp, hp𝔭, hpn⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ 𝔭 ∧ p ∣ n := by
    letI := Ideal.Quotient.field 𝔭
    obtain ⟨p, hch⟩ := CharP.exists (𝓞 E ⧸ 𝔭)
    have hn0 : Ideal.Quotient.mk 𝔭 (n : 𝓞 E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hn𝔭
    rw [map_natCast] at hn0
    have hpn : p ∣ n := (CharP.cast_eq_zero_iff (𝓞 E ⧸ 𝔭) p n).1 hn0
    have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ 𝔭) p).resolve_right (by
      rintro rfl
      rw [zero_dvd_iff] at hpn
      omega)
    refine ⟨p, hp, Ideal.Quotient.eq_zero_iff_mem.1 ?_, hpn⟩
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p
  have hp0 := hp.pos
  have hsmA : ∀ t ∈ 𝔭, ∀ x : X, t • x ∈ img D y Z' 𝔭 := fun t ht x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ht trivial)
  have hpA : ∀ x : X, p • x ∈ img D y Z' 𝔭 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hsmA _ hp𝔭 x
  obtain ⟨c0, hc0⟩ : ∃ c, y c ∉ img D y Z' 𝔭 := by
    by_contra hne
    push_neg at hne
    apply hi
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, e, he⟩ := hc.1 x
    have : x = y a - n • e := by rw [he, add_sub_cancel_right]
    rw [this]
    refine sub_mem (hne a) ?_
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hsmA _ hn𝔭 e
  obtain ⟨a, ha, hac⟩ := exists_pair D hp ((img D y Z' 𝔭).toAddSubgroup.comap y.toAddMonoidHom)
    (fun x => by
      show y (p • x) ∈ img D y Z' 𝔭
      rw [map_nsmul]
      exact hpA _) (c := c0) hc0
  replace ha : ∀ b, y b ∈ img D y Z' 𝔭 → (p : ℤ) ∣ D.EF a b := fun b hb => ha b hb
  have hya : ∃ e, y a = p • e := cois_dvd D y hn hc hpn a fun b ⟨e, he⟩ => ha b (by rw [he]; exact hpA e)
  have hbar : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), H.bar t ∈ 𝔭 := fun t ht => by
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at ht
    have : H.bar.symm t = H.bar t := by
      apply H.bar.injective
      rw [RingEquiv.apply_symm_apply, bar_bar]
    rwa [← this]
  have hta : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ e, t • a = p • e := fun t ht =>
    GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hp0 _ fun c => by
      rw [D.adj]
      apply ha
      rw [map_smul]
      exact hsmA _ (hbar t ht) _
  obtain ⟨z, hz, m, hm, b', hb', rfl⟩ := h.exists_decomp a
  obtain ⟨w1, -, hw1⟩ := mem_nsmul_of_dvd h hp0 hz fun b hb => by
    have := ha b (Submodule.mem_sup_left (Submodule.mem_map_of_mem hb))
    rwa [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hm.2 b hb, h.2.1 hb' b hb, add_zero,
      add_zero] at this
  obtain ⟨w2, hw2⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hp0 m fun c => by
    obtain ⟨zc, hzc, mc, hmc, bc, hbc, rfl⟩ := h.exists_decomp c
    have h1 := ha mc (hL (Submodule.mem_map_of_mem hmc))
    have e1 : D.EF z mc = 0 := by rw [ef_swap, hmc.1 z hz, neg_zero]
    have e2 : D.EF b' mc = 0 := by rw [ef_swap, hmc.2 b' hb', neg_zero]
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, e1, e2, zero_add, add_zero] at h1
    rwa [map_add, map_add, hm.1 zc hzc, hm.2 bc hbc, zero_add, add_zero]
  have hzm : z + m = p • (w1 + w2) := by rw [hw1, hw2, smul_add]
  have hyb : ∃ e, y b' = p • e := by
    obtain ⟨e, he⟩ := hya
    refine ⟨e - y (w1 + w2), ?_⟩
    calc y b' = y (z + m + b') - y (z + m) := by rw [map_add y (z + m) b', add_sub_cancel_left]
      _ = p • (e - y (w1 + w2)) := by rw [he, hzm, map_nsmul, smul_sub]
  have hq : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ e ∈ Z', t • b' = p • e := fun t ht => by
    obtain ⟨e, he⟩ := hta t ht
    have h1 : t • b' = p • (e - t • (w1 + w2)) := by
      calc t • b' = t • (z + m + b') - t • (z + m) := by rw [smul_add t (z + m) b', add_sub_cancel_left]
        _ = p • (e - t • (w1 + w2)) := by rw [he, hzm, smul_comm t p, smul_sub]
    refine ⟨_, (h.symm.isIsoSat).2 p _ hp.ne_zero ?_, h1⟩
    rw [← h1]
    exact Z'.smul_mem t hb'
  haveI := Ideal.map_isMaximal_of_equiv H.bar (p := 𝔭)
  obtain ⟨e, -, he⟩ := mem_nsmul_of_img_eq_top D y Z Z' h hr _ this htop hb' hyb hq
  apply hac
  rw [hzm, he, ← smul_add, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory.LowFilt.CoisBar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmulStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | exact GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | (intros; apply GlobalTheory.LowFilt.ker_mod_eq_perp_range_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOneStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G → q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e → (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧ (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧ e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  first | exact @GlobalTheory.Dieu.le_colength_of_htOne | exact GlobalTheory.Dieu.le_colength_of_htOne | (intros; apply GlobalTheory.Dieu.le_colength_of_htOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyFormula_evenDegeneration_global : KeyGlob := by
  first | exact @GlobalTheory.KeyEvenClosing.keyGlob | exact GlobalTheory.KeyEvenClosing.keyGlob | (intros; apply GlobalTheory.KeyEvenClosing.keyGlob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirstStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_petersson_first : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1)) := by
  first | exact @GlobalTheory.CovTop.ShortSpanUnitCover.short_span_uc | exact GlobalTheory.CovTop.ShortSpanUnitCover.short_span_uc | (intros; apply GlobalTheory.CovTop.ShortSpanUnitCover.short_span_uc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Bijective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective) | (exact GlobalTheory.EtC.gmPhi_bijective) | (intros; apply GlobalTheory.EtC.gmPhi_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  first | (exact @GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (exact GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (intros; apply GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls  <;> assumption)
end

