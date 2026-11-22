import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitDetOfProductMapNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulExactOfGradedRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscrEqJacobianOfIntegralPoints
section
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_basis_det_ne_zero_of_points {O B Ix : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup B] [Module O B] [Fintype Ix] [DecidableEq Ix]
    (φ : B →ₗ[O] (Ix → O)) (hφ : Function.Injective φ) (c : O) (hc : c ≠ 0)
    (hs : ∀ t : Ix → O, ∃ y, φ y = c • t) :
    ∃ b : Module.Basis Ix O B, (Matrix.of fun a a' => φ (b a') a).det ≠ 0 := by
  have hfin : Module.Finite O B := Module.Finite.of_injective φ hφ
  have hfree : Module.Free O B :=
    Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ).symm
  have h1 : Module.finrank O B ≤ Module.finrank O (Ix → O) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have h2 : Module.finrank O (Ix → O) ≤ Module.finrank O (LinearMap.range φ) := by
    let ψ : (Ix → O) →ₗ[O] LinearMap.range φ :=
      LinearMap.codRestrict _ (c • LinearMap.id) (fun t => by
        obtain ⟨y, hy⟩ := hs t
        exact ⟨y, hy⟩)
    refine LinearMap.finrank_le_finrank_of_injective (f := ψ) ?_
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h3 : c • t = 0 := congrArg Subtype.val ht
    exact (smul_eq_zero.1 h3).resolve_left hc
  rw [← (LinearEquiv.ofInjective φ hφ).finrank_eq] at h2
  have h3 : Module.finrank O B = Fintype.card Ix := by
    rw [le_antisymm h1 h2, Module.finrank_fintype_fun_eq_card]
  let b : Module.Basis Ix O B :=
    (Module.finBasisOfFinrankEq O B h3).reindex (Fintype.equivFin Ix).symm
  refine ⟨b, fun h0 => ?_⟩
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h4 : φ (∑ a, v a • b a) = 0 := by
    ext a
    have := congrFun hMv a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [map_sum, Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h5 : ∑ a, v a • b a = 0 := hφ (h4.trans (map_zero φ).symm)
  exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h5))

theorem discr_jacobian_of_points :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix]
      [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O))
      (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) →
      (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) →
      (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) →
      (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) →
      ∃ β : Ix → (MvPowerSeries (Fin g) O),
        (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧
        (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧
        Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2)
          (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det) := by
  intro O _ _ _ _ g Ix _ _ F e hF hX hker ⟨c, hc, hs⟩
  let S := MvPowerSeries (Fin g) O
  let I : Ideal S := Ideal.span (Set.range F)
  let eb : Ix → ((S ⧸ I) →ₐ[O] O) := fun a => Ideal.Quotient.liftₐ I (e a) (fun s hs => by
    have : I ≤ RingHom.ker (e a) := Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact hF a i)
    exact this hs)
  have heb : ∀ a s, eb a (Ideal.Quotient.mk I s) = e a s := fun a s => rfl
  let φ : (S ⧸ I) →ₗ[O] (Ix → O) := LinearMap.pi fun a => (eb a).toLinearMap
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker s fun a => congrFun hy a)
  obtain ⟨b, hb⟩ := exists_basis_det_ne_zero_of_points φ hφ c hc fun t => by
    obtain ⟨G, hG⟩ := hs t
    exact ⟨Ideal.Quotient.mk I G, funext hG⟩
  choose β hβ using fun a => Ideal.Quotient.mk_surjective (b a)
  have hM : (Matrix.of fun a a' => e a (β a')) = Matrix.of fun a a' => eb a (b a') := by
    ext a a'
    rw [Matrix.of_apply, Matrix.of_apply, ← hβ, heb]
  have hb' : (Matrix.of fun a a' => eb a (b a')).det ≠ 0 := hb
  have hq : ∀ (G : S) (r : Ix → O), G - ∑ a, r a • β a ∈ I ↔
      Ideal.Quotient.mk I G = ∑ a, r a • b a := by
    intro G r
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk O, map_sum]
    simp only [map_smul, Ideal.Quotient.mkₐ_eq_mk, hβ]
  refine ⟨β, fun G => ⟨b.equivFun (Ideal.Quotient.mk I G), ?_, fun r hr => ?_⟩, ?_, ?_⟩
  · exact (hq G _).2 (b.sum_equivFun _).symm
  · rw [(hq G r).1 hr, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  · rw [hM]; exact hb'
  · rcases isEmpty_or_nonempty Ix with h | ⟨⟨a⟩⟩
    · simp
    · have hf : ∀ i, MvPowerSeries.constantCoeff (F i) ∈ IsLocalRing.maximalIdeal O := by
        intro i
        obtain ⟨u, hu⟩ := GlobalTheory.DiscrJacobian.exists_eq_C_add_sum (F i)
        have h1 := congrArg (e a) hu
        have h2 : e a (MvPowerSeries.C (MvPowerSeries.constantCoeff (F i)))
            = MvPowerSeries.constantCoeff (F i) := (e a).commutes _
        rw [hF, map_add, h2, map_sum] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm]
        refine neg_mem (Ideal.sum_mem _ fun j _ => ?_)
        rw [map_mul]
        exact Ideal.mul_mem_right _ _ (hX a j)
      have h1 := GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian O g _ F
        (b.reindex (Fintype.equivFin Ix)) hf
      obtain ⟨h2, h3⟩ := discr_norm_eq_of_points O (S ⧸ I) Ix b eb hb'
      rw [Module.Basis.coe_reindex, Algebra.discr_reindex, h2, h3] at h1
      rw [hM]
      exact h1

end GlobalTheory.KeyKa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsCxOfFactor
section
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa.KoszulTors
section Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

end Alg

variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma kosD_inl_indep_ev
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (p : (I : Finset (Fin g)) × Fin (N I.card)) (y : _root_.GlobalTheory.KeyKa.KIx g d N) :
    _root_.GlobalTheory.KeyKa.kosD m ev (.inl p) y = _root_.GlobalTheory.KeyKa.kosD m ev' (.inl p) y := by
  rcases y with q | b <;> rfl

variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma kosD_inr_eq_zero
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (x : _root_.GlobalTheory.KeyKa.KIx g d N) (a : Fin d) :
    _root_.GlobalTheory.KeyKa.kosD m ev x (.inr a) = 0 := by
  rcases x with p | b <;> rfl

variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma map_kosD_inl_inl {S : Type} [CommRing S] (f : R →+* S)
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    {d' : ℕ} (e : ∀ j, Matrix (Fin d') (Fin (N j)) S) (p q : (I : Finset (Fin g)) × Fin (N I.card)) :
    f (_root_.GlobalTheory.KeyKa.kosD m ev (.inl p) (.inl q)) =
      _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map f) e (.inl p) (.inl q) := by
  simp [_root_.GlobalTheory.KeyKa.kosD, map_sum, apply_ite]

theorem _root_.GlobalTheory.KeyKa.KoszulTors.koszul_tors : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O)
    (ev ev₀ : ∀ j, Matrix (Fin d) (Fin (N j)) O) (Pm : Matrix (Fin d) (Fin d) O),
    _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg (_root_.GlobalTheory.KeyKa.kosD m ev) →
    ev 0 = Pm * ev₀ 0 → Pm.det ≠ 0 → Function.Surjective (ev₀ 0).mulVec →
    (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) →
    (∀ v : _root_.GlobalTheory.KeyKa.KIx g 0 N → IsLocalRing.ResidueField O,
      (_root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
        (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (_root_.GlobalTheory.KeyKa.kosD (d := 0)
        (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) →
    _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg (_root_.GlobalTheory.KeyKa.kosD m ev₀) ∧
      ∃ t, _root_.GlobalTheory.KeyKa.TorsSq _root_.GlobalTheory.KeyKa.kdeg
        (_root_.GlobalTheory.KeyKa.kosD m ev₀) t := by
  intro O _ _ _ g d N m ev ev₀ Pm hcx hev hdet hsurj hker hres
  set K := _root_.GlobalTheory.KeyKa.kosD m ev with hK
  set K₀ := _root_.GlobalTheory.KeyKa.kosD m ev₀ with hK₀
  have hrow : ∀ p y, K (.inl p) y = K₀ (.inl p) y := fun p y =>
    kosD_inl_indep_ev m ev ev₀ p y
  have haug : ∀ a y, K (.inr a) y = ∑ b, Pm a b * K₀ (.inr b) y := by
    intro a y
    rcases y with ⟨I, l⟩ | c
    · by_cases hI : I = ∅
      · subst hI
        show ev 0 a l = ∑ b, Pm a b * (if (∅ : Finset (Fin g)) = ∅ then ev₀ 0 b l else 0)
        rw [hev]
        exact Matrix.mul_apply.trans (Finset.sum_congr rfl fun b _ => by rw [if_pos rfl])
      · show (if I = ∅ then ev I.card a l else 0) = ∑ b, Pm a b * (if I = ∅ then ev₀ I.card b l else 0)
        simp [hI]
    · simp [hK, hK₀, kosD_inr_eq_zero]
  have hcx₀ : _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg K₀ := by
    refine ⟨fun x y hxy => ?_, ?_⟩
    · rcases x with p | a
      · rw [← hrow]; exact hcx.1 _ _ hxy
      · rcases y with ⟨I, l⟩ | c
        · have hI : I ≠ ∅ := by
            rintro rfl
            exact hxy rfl
          show (if I = ∅ then ev₀ I.card a l else 0) = 0
          simp [hI]
        · exact kosD_inr_eq_zero m ev₀ _ c
    · have hsq : ∀ x y, ∑ b, K x b * K b y = 0 := fun x y => by
        have := congrFun (congrFun hcx.2 x) y
        simpa [Matrix.mul_apply] using this
      ext x y
      rw [Matrix.mul_apply, Matrix.zero_apply]
      have hmid : ∀ x b, K₀ x b * K₀ b y = K₀ x b * K b y := by
        intro x b
        rcases b with q | c
        · rw [hrow]
        · have hz : K₀ x (.inr c) = 0 := kosD_inr_eq_zero m ev₀ x c
          rw [hz, zero_mul, zero_mul]
      rcases x with p | a
      · rw [← hsq (.inl p) y]
        refine Fintype.sum_congr _ _ fun b => ?_
        rw [hmid, hrow]
      · have hvec : Pm.mulVec (fun b => ∑ c, K₀ (.inr b) c * K₀ c y) = 0 := by
          ext a'
          rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hsq (.inr a') y]
          simp only [Finset.mul_sum, haug, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Fintype.sum_congr _ _ fun c => Fintype.sum_congr _ _ fun b => ?_
          rw [mul_assoc, hmid]
        exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hvec) a
  refine ⟨hcx₀, _root_.GlobalTheory.TorsExists.exists_torsSq O _ _root_.GlobalTheory.KeyKa.kdeg K₀ hcx₀ ?_⟩
  intro v hv
  have hz : ∀ x c, K₀ x (.inr c) = 0 := fun x c => kosD_inr_eq_zero m ev₀ x c
  have hmv : ∀ (u : _root_.GlobalTheory.KeyKa.KIx g d N → IsLocalRing.ResidueField O) y,
      (K₀.map (IsLocalRing.residue O)).mulVec u y = ∑ I : Finset (Fin g), ∑ l : Fin (N I.card),
        IsLocalRing.residue O (K₀ y (.inl ⟨I, l⟩)) * u (.inl ⟨I, l⟩) := by
    intro u y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [Matrix.map_apply, hz]
  have hmv₀ : ∀ (u : _root_.GlobalTheory.KeyKa.KIx g 0 N → IsLocalRing.ResidueField O) y,
      (_root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
        (fun _ => 0)).mulVec u y = ∑ I : Finset (Fin g), ∑ l : Fin (N I.card),
        _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
          (fun _ => 0) y (.inl ⟨I, l⟩) * u (.inl ⟨I, l⟩) := by
    intro u y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp
  have hent : ∀ (p q : (I : Finset (Fin g)) × Fin (N I.card)),
      IsLocalRing.residue O (K₀ (.inl p) (.inl q)) =
        _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
          (fun _ => (0 : Matrix (Fin 0) _ _)) (.inl p) (.inl q) := fun p q =>
    map_kosD_inl_inl _ m ev₀ _ p q

  choose u0 hu0 using fun a : Fin d => IsLocalRing.residue_surjective (v (.inr a))
  obtain ⟨s, hs⟩ := hsurj u0

  choose sa hsa using fun a : Fin d => hsurj (Pi.single a 1)
  choose x hx using fun l : Fin (N 0) => IsLocalRing.residue_surjective (v (.inl ⟨∅, l⟩))
  have hc : ∀ a, IsLocalRing.residue O ((ev₀ 0).mulVec x a) = 0 := by
    intro a
    have h := congrFun hv (.inr a)
    rw [Pi.zero_apply, hmv, Finset.sum_eq_single (∅ : Finset (Fin g))] at h
    · rw [← h]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hx]
      rfl
    · intro I _ hI
      refine Finset.sum_eq_zero fun l _ => ?_
      show IsLocalRing.residue O (if I = ∅ then ev₀ I.card a l else 0) * _ = 0
      simp [hI]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  set s' : Fin (N 0) → O := ∑ a, (ev₀ 0).mulVec x a • sa a with hs'
  have hs'ev : (ev₀ 0).mulVec s' = (ev₀ 0).mulVec x := by
    ext a
    simp [hs', Matrix.mulVec_sum, Matrix.mulVec_smul, hsa, Finset.sum_apply, Pi.single_apply]
  have hs'res : ∀ l, IsLocalRing.residue O (s' l) = 0 := by
    intro l
    simp [hs', Finset.sum_apply, hc]
  have hx'0 : (ev 0).mulVec (x - s') = 0 := by
    rw [hev, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hs'ev, sub_self, Matrix.mulVec_zero]
  obtain ⟨w1, hw1⟩ := hker (x - s') hx'0

  obtain ⟨w', hw'⟩ := hres (Sum.elim (fun p => v (.inl p)) (fun e => Fin.elim0 e)) (by
    ext z
    rcases z with ⟨I, l⟩ | e
    · have h := congrFun hv (.inl ⟨I, l⟩)
      rw [Pi.zero_apply, hmv] at h
      rw [hmv₀, Pi.zero_apply, ← h]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun l' _ => ?_
      rw [hent]
      rfl
    · exact Fin.elim0 e)
  let wf : (I : Finset (Fin g)) → Fin (N I.card) → IsLocalRing.ResidueField O := fun I l =>
    if hI : I = ∅ then IsLocalRing.residue O (s (Fin.cast (by simp [hI]) l))
    else if I.card = 1 then
      ∑ i, (if h : I = {i} then IsLocalRing.residue O (w1 i (Fin.cast (by simp [h]) l)) else 0)
    else w' (.inl ⟨I, l⟩)
  refine ⟨Sum.elim (fun p => wf p.1 p.2) (fun _ => 0), ?_⟩
  ext y
  rcases y with ⟨I, l⟩ | a
  · by_cases hI : I = ∅
    · subst hI
      obtain ⟨l, rfl⟩ : ∃ l' : Fin (N 0), l' = l := ⟨l, rfl⟩
      have hxl : IsLocalRing.residue O (x l) = ∑ i, ∑ l'' : Fin (N 1),
          IsLocalRing.residue O (m i 0 1 l l'') * IsLocalRing.residue O (w1 i l'') := by
        calc IsLocalRing.residue O (x l)
            = IsLocalRing.residue O ((∑ i, (m i 0 1).mulVec (w1 i)) l) := by
              rw [← hw1]
              show _ = IsLocalRing.residue O (x l - s' l)
              simp [hs'res]
          _ = _ := by simp [Finset.sum_apply, Matrix.mulVec, dotProduct, map_sum]
      refine Eq.trans ?_ (hx l)
      rw [hmv, hxl]
      have hJ : ∀ J : Finset (Fin g), ∑ l' : Fin (N J.card),
          IsLocalRing.residue O (K₀ (.inl ⟨∅, l⟩) (.inl ⟨J, l'⟩)) *
            Sum.elim (fun p : (I : Finset (Fin g)) × Fin (N I.card) => wf p.1 p.2)
              (fun _ : Fin d => (0 : IsLocalRing.ResidueField O)) (.inl ⟨J, l'⟩) =
          ∑ i, if J = {i} then ∑ l'' : Fin (N 1),
            IsLocalRing.residue O (m i 0 1 l l'') * IsLocalRing.residue O (w1 i l'') else 0 := by
        intro J
        by_cases h : ∃ i, J = {i}
        · obtain ⟨i, rfl⟩ := h
          rw [Finset.sum_eq_single i (fun j _ hj => if_neg fun h' => hj (Finset.singleton_inj.mp h').symm)
            (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl]
          refine Finset.sum_congr rfl fun l' _ => ?_
          congr 1
          · rw [hK₀]
            first
              | (simp [_root_.GlobalTheory.KeyKa.kosD]; done)
              | (simp [_root_.GlobalTheory.KeyKa.kosD]; rfl)
          · first
              | (simp [wf]; done)
              | (simp [wf]; rfl)
        · push_neg at h
          rw [Finset.sum_eq_zero fun i _ => if_neg (h i)]
          refine Finset.sum_eq_zero fun l' _ => ?_
          rw [hK₀]
          simp [_root_.GlobalTheory.KeyKa.kosD, h]
      rw [Finset.sum_congr rfl fun J _ => hJ J, Finset.sum_comm]
      simp
    · refine Eq.trans ?_ (hw' ⟨I, l⟩ hI).symm
      rw [hmv, hmv₀]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun l' _ => ?_
      by_cases hdeg : J.card = I.card + 1
      · have hJ0 : J ≠ ∅ := by
          rintro rfl
          simp at hdeg
        have hJ1 : J.card ≠ 1 := by
          intro h
          exact hI (Finset.card_eq_zero.mp (by omega))
        rw [hent]
        congr 1
        simp [wf, hJ0, hJ1]
      · have h0 : K₀ (.inl ⟨I, l⟩) (.inl ⟨J, l'⟩) = 0 :=
          hcx₀.1 _ _ (by show J.card + 1 ≠ I.card + 1 + 1; omega)
        rw [← hent, h0, map_zero, zero_mul, zero_mul]
  · rw [hmv, Finset.sum_eq_single (∅ : Finset (Fin g))]
    · rw [← hu0 a, ← hs]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      show IsLocalRing.residue O (if (∅ : Finset (Fin g)) = ∅ then ev₀ 0 a l else 0) * wf ∅ l = _
      first
        | (simp [wf]; done)
        | (simp [wf]; rfl)
        | rfl
        | (simp only [wf, ↓reduceDIte, ↓reduceIte]; rfl)
    · intro I _ hI
      refine Finset.sum_eq_zero fun l _ => ?_
      show IsLocalRing.residue O (if I = ∅ then ev₀ I.card a l else 0) * _ = 0
      simp [hI]
    · intro h'
      exact absurd (Finset.mem_univ _) h'

end GlobalTheory.KeyKa.KoszulTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulExactOfGradedRegularStatement
section
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular : ∀ (K : Type) [CommRing K] (g : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K), (∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2)) → (∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g → (m i j (j + 1)).mulVec y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' j (j + 1)).mulVecLin) → y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' (j + 1) (j + 2)).mulVecLin) → ∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w : KIx g 0 N → K, ∀ p : (Σ I : Finset (Fin g), Fin (N I.card)), p.1 ≠ ∅ → v (.inl p) = (kosD m (fun _ => 0)).mulVec w (.inl p) := by
  first | exact @GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular | exact GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular | (intros; apply GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
section
noncomputable section

open Complex Matrix

namespace GlobalTheory

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end General

variable {g : ℕ}

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.isSymm_phSym (x : Matrix (Fin g) (Fin g) ℂ) : (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x).IsSymm := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  ext i j
  simp only [transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.phSym_eq_self_of_isSymm {x : Matrix (Fin g) (Fin g) ℂ} (hx : x.IsSymm) :
    _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  rw [hx.eq, ← two_smul ℂ x, smul_smul]
  norm_num

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.differentiable_phSym_coords :
    Differentiable ℂ (fun x : Fin g → Fin g → ℂ =>
      (Matrix.of.symm (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) : Fin g → Fin g → ℂ)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul]
  fun_prop

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.isOpen_phDom (g : ℕ) : IsOpen (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hc : Continuous (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; fun_prop
  rw [isOpen_iff_mem_nhds]
  intro x hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom at hx ⊢
  have hx' : _root_.GlobalTheory.IsSiegel (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := _root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hx
  have h := hc.continuousAt.eventually hx'.eventually_isSiegel
  filter_upwards [h] with y hy
  exact _root_.GlobalTheory.isSiegel_iff_mem_siegelH.1 (hy (_root_.GlobalTheory.isSymm_phSym _))

open Complex Matrix in
variable {g : ℕ} in
private theorem convex_siegelH (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) := by
  intro A hA B hB a b ha hb hab
  rw [← _root_.GlobalTheory.isSiegel_iff_mem_siegelH] at *
  refine ⟨?_, ?_⟩
  · exact (hA.isSymm.smul a).add (hB.isSymm.smul b)
  · have hm : ((a • A + b • B).map Complex.im) = a • A.map Complex.im + b • B.map Complex.im := by
      ext i j; simp
    rw [hm]
    rcases ha.eq_or_lt with rfl | ha'
    · simp at hab; subst hab; simpa using hB.posDef
    · exact (hA.posDef.smul ha').add_posSemidef (hB.posDef.posSemidef.smul hb)

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.convex_phDom (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hl : IsLinearMap ℝ (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    constructor
    · intro x y; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp; ring
    · intro c x; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp; ring
  have := (convex_siegelH g).is_linear_preimage hl
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  exact this

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.of_symm_mem_phDom {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) :
    (Matrix.of.symm τ : Fin g → Fin g → ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  show _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of (Matrix.of.symm τ)) ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)
  rw [Equiv.apply_symm_apply,
    _root_.GlobalTheory.phSym_eq_self_of_isSymm (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm]
  exact hτ

end GlobalTheory
end
end

