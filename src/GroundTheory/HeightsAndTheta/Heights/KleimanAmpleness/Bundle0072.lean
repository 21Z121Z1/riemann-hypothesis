import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

section

variable {k : Type} [Field k] {N m : ℕ}

theorem weight_mapDomain_base (e : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (graphIdx N m))
        (Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e) =
      Sum.elim (fun _ => e.degree) (fun _ => 0) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  funext c
  rw [← sum_block_eq_blockWeight]
  rcases c with ⟨⟩ | ⟨⟩
  · simp only [Sum.elim_inl]
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl fun a _ => Finsupp.mapDomain_apply hinj e a
  · simp only [Sum.elim_inr]
    refine Finset.sum_eq_zero fun b _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨a, ha⟩
    cases (Sigma.mk.inj ha).1

theorem rename_base_homogeneousComponent (d : ℕ) (f : Kleiman.Poly k N) :
    rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (homogeneousComponent d f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (Sum.elim (fun _ => d) (fun _ => 0))
        (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj, coeff_homogeneousComponent,
      weight_mapDomain_base]
    by_cases hd : e.degree = d
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (congrFun h (Sum.inl ()))]
  · push Not at he
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

end

theorem CurveComap.proof (hR : SectionRatio.Statement) (hD : RatioDim.Statement) : CurveComap.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle e
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
  have hdim := hD k N m W hW.isPrime hW.multiHomog j hj fun b => by
    obtain ⟨d, f, g, -, -, h1, h2⟩ := hR k N Ω x Q n m s hx hgen W hW hle j b hj
    exact ⟨f, g, h1, h2⟩
  have hsub : Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) e ↔
      ringKrullDim (Kleiman.Poly k N ⧸
          W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) =
        ((e + 1 : ℕ) : WithBot ℕ∞) := by
    refine ⟨fun h => h.dim, fun h => ⟨Ideal.comap_isPrime _ _, fun f hf d => ?_, ?_, ?_, h⟩⟩
    · rw [Ideal.mem_comap] at hf ⊢
      rw [rename_base_homogeneousComponent]
      exact hW.multiHomog _ hf _
    · rw [← comap_mIdealOver_graph (S := k) x s]
      exact Ideal.comap_mono hle
    · obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
      have hXi : rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i : Kleiman.Poly k N) =
          X ⟨baseBlock, i⟩ := rename_X _ _
      exact ⟨i, by rw [Ideal.mem_comap, hXi]; exact hi⟩
  rw [hsub, FieldNumbers.CutRegular.relDim_eq_natCast_iff, hdim, Fintype.card_sum, Fintype.card_unit]
  generalize ringKrullDim (Kleiman.Poly k N ⧸
    W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) = D
  induction D using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe t =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj,
      WithBot.coe_inj]
    induction t using ENat.recTopCoe with
    | top => exact iff_of_false (by rw [top_add]; exact ENat.top_ne_natCast _) (ENat.top_ne_natCast _)
    | coe t =>
      norm_cast
      omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SgnSingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

namespace CechContract

section Comb

variable {n : ℕ} {M : Type*} [AddCommGroup M]

theorem sgn_insert {J : Finset (Fin n)} {a : Fin n} (ha : a ∉ J) (j : Fin n) :
    Kleiman.Cech.sgn (insert a J) j = if a < j then -Kleiman.Cech.sgn J j else Kleiman.Cech.sgn J j := by
  unfold Kleiman.Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ]; ring
  · rfl

theorem sgn_mul_self (J : Finset (Fin n)) (j : Fin n) : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn J j = 1 := by
  unfold Kleiman.Cech.sgn
  rw [← mul_pow]; norm_num

theorem sgn_singleton (j : Fin n) : Kleiman.Cech.sgn {j} j = 1 := by
  rw [Kleiman.Cech.sgn, Finset.filter_singleton, if_neg (lt_irrefl j)]; simp

def cD (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  ∑ j ∈ J, Kleiman.Cech.sgn J j • f (J.erase j)

def cH (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  if j₀ ∈ J then 0 else Kleiman.Cech.sgn (insert j₀ J) j₀ • f (insert j₀ J)

theorem cD_cH_add (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) :
    cD (cH j₀ f) J + cH j₀ (cD f) J = f J := by
  by_cases h₀ : j₀ ∈ J
  · have hH : cH j₀ (cD f) J = 0 := if_pos h₀
    have hrest : ∑ j ∈ J.erase j₀, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hj, -⟩ := Finset.mem_erase.mp hj
      rw [cH, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hj, h₀⟩), smul_zero]
    rw [hH, add_zero, cD, ← Finset.add_sum_erase J _ h₀, hrest, add_zero, cH,
      if_neg (Finset.notMem_erase j₀ J), Finset.insert_erase h₀, smul_smul, sgn_mul_self, one_smul]
  · have hsum : ∑ j ∈ J, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) +
        ∑ j ∈ J, Kleiman.Cech.sgn (insert j₀ J) j₀ • Kleiman.Cech.sgn (insert j₀ J) j •
          f ((insert j₀ J).erase j) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj₀ : j ≠ j₀ := fun h => h₀ (h ▸ hj)
      have hn : j₀ ∉ J.erase j := fun h => h₀ (Finset.mem_of_mem_erase h)
      have e : insert j₀ (J.erase j) = (insert j₀ J).erase j := (Finset.erase_insert_of_ne (Ne.symm hj₀)).symm
      have s1 : Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ = Kleiman.Cech.sgn (J.erase j) j₀ := by
        rw [← e, sgn_insert hn, if_neg (lt_irrefl _)]
      have s2 : Kleiman.Cech.sgn (insert j₀ J) j₀ = Kleiman.Cech.sgn J j₀ := by
        rw [sgn_insert h₀, if_neg (lt_irrefl _)]
      have s3 := sgn_insert h₀ j
      have s4 : Kleiman.Cech.sgn J j₀ =
          if j < j₀ then -Kleiman.Cech.sgn (J.erase j) j₀ else Kleiman.Cech.sgn (J.erase j) j₀ := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact sgn_insert (Finset.notMem_erase j J) j₀
      have hc : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ +
          Kleiman.Cech.sgn (insert j₀ J) j₀ * Kleiman.Cech.sgn (insert j₀ J) j = 0 := by
        rw [s1, s2, s3, s4]
        rcases lt_or_gt_of_ne hj₀ with h | h
        · rw [if_neg (lt_asymm h), if_pos h]; ring
        · rw [if_pos h, if_neg (lt_asymm h)]; ring
      rw [cH, if_neg hn, e, smul_smul, smul_smul, ← add_smul, hc, zero_smul]
    have hH : cH j₀ (cD f) J = Kleiman.Cech.sgn (insert j₀ J) j₀ • cD f (insert j₀ J) := if_neg h₀
    rw [hH]
    unfold cD
    rw [Finset.sum_insert h₀, Finset.erase_insert h₀, smul_add, smul_smul, sgn_mul_self, one_smul,
      Finset.smul_sum, add_left_comm, hsum, add_zero]

end Comb

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

open Classical in

noncomputable def extZ {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (K : Finset (Fin (N + 1))) : Ω :=
  if h : K.Nonempty ∧ K ⊆ Kleiman.support x ∧ K.card = p + 1 then s ⟨⟨K, h.1, h.2.1⟩, h.2.2⟩ else 0

theorem extZ_idx {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : extZ s I.1.1 = s I := by
  rw [extZ, dif_pos ⟨I.1.2.1, I.1.2.2, I.2⟩]

theorem d_eq {p : ℕ} (t : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p) (g : Finset (Fin (N + 1)) → Ω)
    (hg : ∀ I, t I = g I.1.1) (J : Kleiman.Cech.Idx (Kleiman.support x) (p + 1)) :
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t J = cD g J.1.1 := by
  rw [Kleiman.Cech.d_apply, cD,
    ← Finset.sum_coe_sort J.1.1 (fun j => Kleiman.Cech.sgn J.1.1 j • g (J.1.1.erase j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ • t (Kleiman.Cech.face J j) = _ • g (Kleiman.Cech.face J j).1.1
  rw [hg]

def insIdx {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ} (I : Kleiman.Cech.Idx (Kleiman.support x) p)
    (h : j₀ ∉ I.1.1) : Kleiman.Cech.Idx (Kleiman.support x) (p + 1) :=
  ⟨⟨insert j₀ I.1.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀ I.1.2.2⟩, by
    rw [Finset.card_insert_of_notMem h, I.2]⟩

theorem cH_cD_extZ {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ}
    (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (hds : Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p s = 0)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : cH j₀ (cD (extZ s)) I.1.1 = 0 := by
  unfold cH
  split_ifs with h
  · rfl
  · have h1 := d_eq S s (extZ s) (fun I => (extZ_idx s I).symm) (insIdx hj₀ I h)
    rw [hds] at h1
    change _ • cD (extZ s) (insIdx hj₀ I h).1.1 = 0
    rw [← h1, Pi.zero_apply, smul_zero]

end CechSide

theorem proof : Statement := by
  intro S _ Ω _ _ N x G J₀ hcard hmono hadd
  obtain ⟨j₀, hJ₀⟩ := Finset.card_eq_one.mp hcard
  have hj₀U : j₀ ∈ Kleiman.support x := J₀.2.2 (hJ₀ ▸ Finset.mem_singleton_self j₀)
  have hG : ∀ J J' : Kleiman.Chart x, J'.1 = insert j₀ J.1 → G J' = G J := fun J J' h =>
    hadd J J' (by rw [h, hJ₀, Finset.insert_eq])
  refine ⟨fun J => ?_, fun s hs hds => ?_, fun p s hs hds => ?_⟩
  · let J' : Kleiman.Chart x := ⟨insert j₀ J.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀U J.2.2⟩
    rw [← hG J J' rfl]
    exact hmono J₀ J' (by
      rw [hJ₀]; exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  · refine ⟨s ⟨J₀, hcard⟩, (hs ⟨J₀, hcard⟩ (Set.mem_univ _) :), fun J => ?_⟩
    have eb : extZ s {j₀} = s ⟨J₀, hcard⟩ :=
      (congrArg (extZ s) hJ₀).symm.trans (extZ_idx s ⟨J₀, hcard⟩)
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp J.2
    have e1 : cD (cH j₀ (extZ s)) J.1.1 = extZ s {j₀} := by
      rw [hj, cD, Finset.sum_singleton, Finset.erase_singleton, sgn_singleton, one_smul, cH,
        if_neg (Finset.notMem_empty _), insert_empty_eq, sgn_singleton, one_smul]
    rw [← extZ_idx s J, ← cD_cH_add j₀ (extZ s) J.1.1, cH_cD_extZ S hj₀U s hds J, add_zero, e1, eb]
  · refine ⟨fun I => cH j₀ (extZ s) I.1.1, fun I _ => ?_, ?_⟩
    · show cH j₀ (extZ s) I.1.1 ∈ G I.1
      unfold cH
      split_ifs with h
      · exact zero_mem _
      · have hK : s (insIdx hj₀U I h) ∈ G (insIdx hj₀U I h).1 := hs _ (Set.mem_univ _)
        rw [← extZ_idx s (insIdx hj₀U I h), hG I.1 (insIdx hj₀U I h).1 rfl] at hK
        exact zsmul_mem hK _
    · funext J
      rw [d_eq S _ (cH j₀ (extZ s)) (fun _ => rfl)]
      have := cD_cH_add j₀ (extZ s) J.1.1
      rw [cH_cD_extZ S hj₀U s hds J, add_zero, extZ_idx] at this
      exact this

end CechContract

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperComponentMulX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

section Lemmas

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem snapper_component_mul_X [DecidableEq K] (f : MvPolynomial (Σ k, ι k) F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (b + NumbersDVR.blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have key : ∀ (φ : MvPolynomial (Σ k, ι k) F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) φ c :
        MvPolynomial (Σ k, ι k) F) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (NumbersDVR.blockWeight ι) φ c
  rw [key, key] at h
  exact h

omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem snapper_colon_X [DecidableEq K] {J : Ideal (MvPolynomial (Σ k, ι k) F)} (hJ : NumbersDVR.IsMultiHomogIdeal J)
    (v : Σ k, ι k) : NumbersDVR.IsMultiHomogIdeal (J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← snapper_component_mul_X]
  exact hJ _ hf _

omit [Fintype K] [LinearOrder K] in

theorem snapper_eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ), eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

theorem snapper_top (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (n : ℕ)
    (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem snapper_finite (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (V : Ideal (MvPolynomial (Σ k, ι k) F))
    (hV : NumbersDVR.IsMultiHomogIdeal V) (m : K → ℤ) (i : ℕ) :
    FiniteDimensional F (cechHc ι (quotPart F V) m i) :=
  (hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance
    (HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV))).1 m i

end Lemmas

theorem EulerPoly.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hE : EulerVar.Statement)
    (hD : PolyOfDiffsExact.Statement) : EulerPoly.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hfin : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F J) m i) :=
    fun J hJ => snapper_finite hS J hJ
  have key : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p := by
    intro J hJ
    refine IsNoetherian.induction (P := fun J : Ideal (MvPolynomial (Σ k, ι k) F) =>
      NumbersDVR.IsMultiHomogIdeal J → ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p)
      (fun J ih hJ => ?_) J hJ
    have hlt2 : ∀ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J →
        J < J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)} := fun v hvJ =>
      lt_of_le_of_ne le_sup_left fun h => hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hSup : ∀ v : Σ k, ι k, NumbersDVR.IsMultiHomogIdeal (J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) :=
      fun v => FieldNumbers.isMultiHomogIdeal_sup_span hJ (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
    by_cases hA : ∃ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J ∧
        J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) ≠ J
    · obtain ⟨v, hvJ, hne⟩ := hA
      have hle : J ≤ J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) := fun f hf => by
        rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
        exact Ideal.mul_mem_right _ J hf
      obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (snapper_colon_X hJ v)
      obtain ⟨p2, hp2⟩ := ih _ (hlt2 v hvJ) (hSup v)
      refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, fun m => ?_⟩
      rw [hE F K ι J v hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ v)) (hfin _ (hSup v)) m, hp1, hp2, map_add,
        ← snapper_eval_shift]
    · push Not at hA
      by_cases hB : ∃ k, ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ J
      · obtain ⟨k, hk⟩ := hB
        refine ⟨0, fun m => ?_⟩
        rw [map_zero, eulerChar]
        refine Finset.sum_eq_zero fun i _ => ?_
        have := cechHc_subsingleton_of_block hk m i
        rw [Module.finrank_zero_of_subsingleton]
        simp
      · push Not at hB
        refine hD K (eulerChar F ι J) fun k => ?_
        obtain ⟨i, hi⟩ := hB k
        obtain ⟨q, hq⟩ := ih _ (hlt2 ⟨k, i⟩ hi) (hSup ⟨k, i⟩)
        refine ⟨q, fun m => ?_⟩
        have h := hE F K ι J ⟨k, i⟩ hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ _)) (hfin _ (hSup _)) m
        rw [hA _ hi] at h
        rw [← hq m]
        linarith
  obtain ⟨p, hp⟩ := key V hV
  exact ⟨∑ k, (Fintype.card (ι k) - 1), p, hfin V hV, fun m i hi => snapper_top V m i hi, hp⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ a, Fintype (ι a)] {k : Type} [Field k]

omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in

theorem X_mem_mIdealOver_iff {Ω : Type} [Field Ω] [Algebra k Ω] (y : (Σ a, ι a) → Ω) (p : Σ a, ι a) :
    (X p : NumbersDVR.MRing ι k) ∈ mIdealOver k y ↔ y p = 0 := by
  change mConeMapOver k y (X p) = 0 ↔ _
  simp [mConeMapOver, X_ne_zero]

def genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] :
    (Σ a, ι a) → FractionRing (NumbersDVR.MRing ι k ⧸ W) :=
  fun p => algebraMap _ _ (Ideal.Quotient.mk W (X p))

omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in

theorem aeval_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (g : NumbersDVR.MRing ι k) :
    aeval (genPtOf W) g = algebraMap _ (FractionRing (NumbersDVR.MRing ι k ⧸ W)) (Ideal.Quotient.mk W g) := by
  have h : (aeval (genPtOf W) : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W)) =
      (IsScalarTower.toAlgHom k (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).comp
        (Ideal.Quotient.mkₐ k W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPtOf]
  exact congrArg (fun φ : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W) => φ g) h

theorem mIdealOver_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (hh : NumbersDVR.IsMultiHomogIdeal W) :
    mIdealOver k (genPtOf W) = W := by
  have hz : ∀ g, aeval (genPtOf W) g = 0 ↔ g ∈ W := fun g => by
    rw [aeval_genPtOf, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).eq_iff'
      (map_zero _)
  ext f
  change mConeMapOver k (genPtOf W) f = 0 ↔ f ∈ W
  constructor
  · intro h
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => (hz _).mp ?_
    rw [← coeff_mConeMapOver, h, coeff_zero]
  · intro hf
    ext e
    rw [coeff_zero, ← Finsupp.equivFunOnFinite_symm_coe e, coeff_mConeMapOver]
    exact (hz _).mpr (hh f hf _)

end Generic

theorem DegEq.proof (hGR : GraphRestrict.Statement) (hIR : Kleiman.InterNumRestrict.Statement.{0, 0})
    (hNM : NumModel.Statement) : DegEq.Statement := by
  intro k _ N Ω _ _ x Q n m s _ hgen pp W hsub hW hle hcomap
  classical
  have := hW.isPrime
  have hWy : mIdealOver k (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  let x' : Fin (N + 1) → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun a => genPtOf W ⟨Sum.inl (), a⟩
  let s' : Fin m → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun b => genPtOf W ⟨Sum.inr (), b⟩
  have hy : graphVec x' s' = genPtOf W := by
    funext p
    rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing (graphIdx N m) k) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := k), hWy]
  have hxy : ∀ i, x' i ≠ 0 → x i ≠ 0 := fun i h h0 =>
    h ((hzero _).mpr (hle ((X_mem_mIdealOver_iff (graphVec x s) ⟨Sum.inl (), i⟩).mpr h0)))
  have hx' : ∃ i, x' i ≠ 0 := by
    obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hs' : ∃ j, s' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
    exact ⟨j, fun h => hj ((hzero _).mp h)⟩
  have hyW : mIdealOver k (graphVec x' s') = W := by rw [hy]; exact hWy
  have hleW : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') := hyW.symm ▸ hle
  have hpp : Kleiman.primeOf (S := k) x' = pp := by
    rw [← comap_mIdealOver_graph (S := k) x' s', hyW, hcomap]
  obtain ⟨Q', r, hR, hgen'⟩ := hGR k N Ω x Q n m s _ x' s' hxy hgen hleW hx' hs'
  have hsub' : Kleiman.IsSubvar x' pp 1 := ⟨hsub.isPrime, hsub.homog, le_of_eq hpp, hsub.relevant, hsub.dim⟩
  have h1 := hIR k Ω N x _ x' hxy (hsub.le.trans hpp.ge) pp 1 hsub' ![Q] ![Q'] (fun _ => r)
    (fun i => by fin_cases i; exact hR)
  have h2 := hNM k (Unit ⊕ Unit) (graphIdx N m) _ (graphVec x' s') baseBlock N (Equiv.refl _) x' rfl
    (GraphModel.full k N _ x' Q' n m s' hx' hgen') 1 ![Q'] ![graphDeg n]
    (fun i => by fin_cases i; exact realises_graph Q' n s' hgen') (by rw [hpp]; exact hsub')
  rw [hyW, hpp] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

