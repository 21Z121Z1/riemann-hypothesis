import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0012
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
section
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeTransfer

section Words

variable {R : Type*} [Ring R]

theorem word_one (l : List R) : word (1 : R) l = l.prod := by
  induction l with
  | nil => rw [word_nil, List.prod_nil]
  | cons a l ih => rw [word_cons, ih, List.prod_cons, one_mul]

theorem word_mul_idem {E : R} (hE : E * E = E) (l : List R) : word E l * E = word E l := by
  induction l with
  | nil => rw [word_nil, hE]
  | cons a l ih => rw [word_cons, mul_assoc, ih]

theorem sum_reverse_eq_zero {M : ℕ} (b : Fin M → R) (h : stdPoly (1 : R) b = 0) :
    ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod = 0 := by
  have h' : ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod = 0 := by
    rw [← h]
    unfold CompanionTheory.D.gk.admitted.stdPoly
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [word_one, zsmul_eq_mul]
  have hrev : ∀ f : Fin M → R, (List.ofFn f).reverse = List.ofFn fun i => f i.rev := by
    intro f
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp only [Fin.val_rev]
      simp only [List.length_reverse, List.length_ofFn] at h1
      omega
  have hsq : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) *
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  calc ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod
      = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ((Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [hrev, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, mul_comm (Equiv.Perm.sign π : ℤ),
          ← mul_assoc, hsq, one_mul]
        all_goals rfl
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod := by
        rw [Finset.smul_sum]
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulRight Fin.revPerm)
          (fun π : Equiv.Perm (Fin M) => (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod)
    _ = 0 := by rw [h', smul_zero]

end Words

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def phi (K : Subgroup G) (σ : G →* (H →L[ℂ] H)) (v : H) : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ fun x : G ⧸ K => σ (Quotient.out x) v

abbrev dlt (K : Subgroup G) : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}

theorem phi_single (hv : ∀ k ∈ K, σ k v = v) (x : G) (c : ℂ) :
    phi K σ v (Finsupp.single (x : G ⧸ K) c) = c • σ x v := by
  rw [phi, Finsupp.linearCombination_single]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk, map_mul, ContinuousLinearMap.mul_apply, hv k k.2]

theorem lam_single (g x : G) (c : ℂ) :
    lam K g (Finsupp.single (x : G ⧸ K) c) = Finsupp.single ((g * x : G) : G ⧸ K) c := by
  simp only [CompanionTheory.Rg.Fl.lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    MulAction.Quotient.smul_mk, smul_eq_mul]

theorem phi_lam (hv : ∀ k ∈ K, σ k v = v) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ v (lam K g f) = σ g (phi K σ v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [lam_single, phi_single hv, phi_single hv, map_mul, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.map_smul]

theorem lam_dlt {k : G} (hk : k ∈ K) : lam K k (dlt K) = dlt K := by
  simp only [dlt]
  rw [lam_single, mul_one]
  congr 1
  exact QuotientGroup.eq.2 (by simpa using K.inv_mem hk)

theorem hk_comm (h : Hk K) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    lam K g ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (lam K g f) := by
  have hc := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact congrArg (fun T : Module.End ℂ ((G ⧸ K) →₀ ℂ) => T f) hc

theorem phi_fixed (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) :
    ∀ k ∈ K, σ k (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  intro k hk
  rw [← phi_lam hv, hk_comm, lam_dlt hk]

theorem phi_phi (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) f =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hd : lam K x (dlt K) = Finsupp.single (x : G ⧸ K) 1 := by
      simp only [dlt]
      rw [lam_single, mul_one]
    rw [phi_single (phi_fixed hv h), ← phi_lam hv, hk_comm, hd,
      ← Finsupp.smul_single_one (x : G ⧸ K) c, LinearMap.map_smul, LinearMap.map_smul]

theorem avg_sigma {E : H →L[ℂ] H} (hA : IsAvg σ K E) (hv : ∀ k ∈ K, σ k v = v) (g : G) (T : Hk K)
    (S : Finset (G ⧸ K)) (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K))
    (hT : (T : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) :
    E (σ g v) = phi K σ v ((((S.card : ℂ)⁻¹ • T : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  have hcard : (S.card : ℂ) ≠ 0 := by
    have hmem : (g : G ⧸ K) ∈ S := by
      have : (g : G ⧸ K) ∈ (↑S : Set (G ⧸ K)) := by
        rw [hS]
        exact MulAction.mem_orbit_self _
      exact Finset.mem_coe.1 this
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨_, hmem⟩).ne'
  have hterm : ∀ y ∈ S, E (phi K σ v (Finsupp.single y 1)) = E (σ g v) := by
    intro y hy
    have hy' : y ∈ MulAction.orbit K (g : G ⧸ K) := by
      rw [← hS]
      exact hy
    obtain ⟨k, rfl⟩ := hy'
    show E (phi K σ v (Finsupp.single (((k : G) * g : G) : G ⧸ K) 1)) = E (σ g v)
    rw [phi_single hv, one_smul, map_mul,
      ContinuousLinearMap.mul_apply, hA.2.2 _ _ k.2]
  have hfix := phi_fixed hv (((S.card : ℂ)⁻¹ • T : Hk K))
  rw [← hA.2.1 _ hfix, Subalgebra.coe_smul, LinearMap.smul_apply, hT]
  simp only [map_smul, map_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

theorem word_apply {E : H →L[ℂ] H} (hA : IsAvg σ K E) (b : G → Hk K)
    (hb : ∀ (u : H), (∀ k ∈ K, σ k u = u) → ∀ g, E (σ g u) = phi K σ u ((b g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)))
    (hv : ∀ k ∈ K, σ k v = v) (l : List G) :
    word E (l.map fun g => σ g) v =
      phi K σ v ((((l.map b).reverse.prod : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  induction l with
  | nil =>
    simp only [List.map_nil, word_nil, List.reverse_nil, List.prod_nil, OneMemClass.coe_one,
      Module.End.one_apply, dlt, phi_single hv, one_smul, map_one, ContinuousLinearMap.one_apply]
    exact hA.2.1 v hv
  | cons g l ih =>
    simp only [List.map_cons, word_cons, ContinuousLinearMap.mul_apply]
    rw [ih, hb _ (phi_fixed hv _) g, phi_phi hv]
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      MulMemClass.coe_mul, Module.End.mul_apply]

theorem stTransfer : StTransfer := by
  intro G _ K M hK hPI H _ _ _ σ _ E hA g
  obtain ⟨T, hT, -, -⟩ := GlobalTheory.T.hecke_operators_span_and_faithful G K hK
  have hfin : ∀ x : G, (MulAction.orbit K (x : G ⧸ K)).Finite := hK
  let S : G → Finset (G ⧸ K) := fun x => (hfin x).toFinset
  have hS : ∀ x, (↑(S x) : Set (G ⧸ K)) = MulAction.orbit K (x : G ⧸ K) :=
    fun x => (hfin x).coe_toFinset
  let b : G → Hk K := fun x => (((S x).card : ℂ)⁻¹ • T x : Hk K)
  have hb : ∀ u : H, (∀ k ∈ K, σ k u = u) → ∀ x, E (σ x u) =
      phi K σ u ((b x : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) :=
    fun u hu x => avg_sigma hA hu x (T x) (S x) (hS x) (hT x (S x) (hS x))
  have hEE : E * E = E := by
    ext v
    exact hA.2.1 (E v) (hA.1 v)
  have hpoly : stdPoly E (fun i => σ (g i)) * E = stdPoly E (fun i => σ (g i)) := by
    unfold CompanionTheory.D.gk.admitted.stdPoly
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [mul_assoc, word_mul_idem hEE]
  have key : ∀ u : H, (∀ k ∈ K, σ k u = u) → (stdPoly E fun i => σ (g i)) u = 0 := by
    intro u hu
    let A : (H →L[ℂ] H) →+ H :=
      { toFun := fun W => W u, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let L : Hk K →+ H :=
      { toFun := fun h => phi K σ u ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)),
        map_zero' := by simp,
        map_add' := fun x y => by simp [map_add] }
    have hw : ∀ π : Equiv.Perm (Fin M), A (word E (List.ofFn fun i => σ (g (π i)))) =
        L (List.ofFn fun i => b (g (π i))).reverse.prod := by
      intro π
      have := word_apply hA b hb hu (List.ofFn fun i => g (π i))
      rw [List.map_ofFn, List.map_ofFn] at this
      exact this
    have h0 := sum_reverse_eq_zero (fun i => b (g i)) (hPI _)
    show A (stdPoly E fun i => σ (g i)) = 0
    unfold CompanionTheory.D.gk.admitted.stdPoly
    rw [map_sum]
    calc ∑ π : Equiv.Perm (Fin M), A (↑↑(Equiv.Perm.sign π) * word E (List.ofFn fun i => σ (g (π i))))
        = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • L (List.ofFn fun i => b (g (π i))).reverse.prod := by
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [← zsmul_eq_mul, map_zsmul, hw]
      _ = L (∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (g (π i))).reverse.prod) := by
          rw [map_sum]
          simp only [map_zsmul]
      _ = 0 := by rw [h0, map_zero]
  ext v
  rw [ContinuousLinearMap.zero_apply, ← hpoly, ContinuousLinearMap.mul_apply]
  exact key _ (hA.1 v)

end GlobalTheory.CompanionTheory.HeckeTransfer
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
section
noncomputable section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.FlWitt

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}

theorem h_zero_right (hh : IsHerm s h) (x : V) : h x 0 = 0 := by
  simpa using hh.2.1 0 x 0

theorem h_zero_left (hh : IsHerm s h) (x : V) : h 0 x = 0 := by
  rw [hh.2.2.1 x 0, h_zero_right hh, map_zero]

theorem h_sum_right (hh : IsHerm s h) {ι : Type} (t : Finset ι) (x : V) (c : ι → L) (v : ι → V) :
    h x (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * h x (v i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h_zero_right hh x
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hh.1, hh.2.1, ih]

def pairMap (e f : Fin l → V) : ((Fin l → L) × (Fin l → L)) →ₗ[L] V where
  toFun p := ∑ i, p.1 i • e i + ∑ i, p.2 i • f i
  map_add' p r := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c p := by
    simp [mul_smul, Finset.smul_sum, smul_add]

theorem pairMap_apply (e f : Fin l → V) (p : (Fin l → L) × (Fin l → L)) :
    pairMap e f p = ∑ i, p.1 i • e i + ∑ i, p.2 i • f i := rfl

theorem pair_e (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (e j) (pairMap e f p) = p.2 j * δ := by
  rw [pairMap_apply, hh.1, h_sum_right hh, h_sum_right hh]
  simp [he, hef]

theorem pair_f (hh : IsHerm s h) {e f : Fin l → V} (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) (j : Fin l)
    (p : (Fin l → L) × (Fin l → L)) : h (f j) (pairMap e f p) = p.1 j * s δ := by
  have hfe : ∀ i, h (f j) (e i) = if i = j then s δ else 0 := by
    intro i
    rw [hh.2.2.1 (e i) (f j), hef]
    split_ifs <;> simp
  rw [pairMap_apply, hh.1, h_sum_right hh, h_sum_right hh]
  simp [hf, hfe]

theorem pair_form (hh : IsHerm s h) {e f : Fin l → V} (he : ∀ i j, h (e i) (e j) = 0)
    (hf : ∀ i j, h (f i) (f j) = 0) (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0)
    (p r : (Fin l → L) × (Fin l → L)) :
    h (pairMap e f p) (pairMap e f r) =
      ∑ j, r.1 j * s (p.2 j * δ) + ∑ j, r.2 j * s (p.1 j * s δ) := by
  have e1 : ∀ j, h (pairMap e f p) (e j) = s (p.2 j * δ) := fun j => by
    rw [hh.2.2.1 (e j), pair_e hh he hef]
  have e2 : ∀ j, h (pairMap e f p) (f j) = s (p.1 j * s δ) := fun j => by
    rw [hh.2.2.1 (f j), pair_f hh hf hef]
  rw [pairMap_apply e f r, hh.1, h_sum_right hh, h_sum_right hh]
  simp only [e1, e2]

theorem pairMap_injective (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V}
    (he : ∀ i j, h (e i) (e j) = 0) (hf : ∀ i j, h (f i) (f j) = 0)
    (hef : ∀ i j, h (e i) (f j) = if i = j then δ else 0) :
    Function.Injective (pairMap e f : ((Fin l → L) × (Fin l → L)) →ₗ[L] V) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  have hb : ∀ j, p.2 j = 0 := fun j => by
    have := pair_e hh he hef j p
    rw [hp, h_zero_right hh] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hd
  have ha : ∀ j, p.1 j = 0 := fun j => by
    have := pair_f hh hf hef j p
    rw [hp, h_zero_right hh] at this
    exact (mul_eq_zero.1 this.symm).resolve_right ((map_ne_zero s).2 hd)
  exact Prod.ext (funext ha) (funext hb)

theorem mem_of_perp (hh : IsHerm s h) (hd : δ ≠ 0) {e f : Fin l → V} {W : Submodule L V}
    (F : IsFrame h δ e f W) (x : V) (h1 : ∀ i, h (e i) x = 0) (h2 : ∀ i, h (f i) x = 0) : x ∈ W := by
  obtain ⟨he, hf, hef, hW, -, hdec⟩ := F
  obtain ⟨a, b, w, hw, rfl⟩ := hdec x
  have hx : ∑ i, a i • e i + ∑ i, b i • f i = pairMap e f (a, b) := rfl
  rw [hx] at h1 h2 ⊢
  have hb : ∀ j, b j = 0 := fun j => by
    have := h1 j
    rw [hh.1, pair_e hh he hef, (hW w hw j).1, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right hd
  have ha : ∀ j, a j = 0 := fun j => by
    have := h2 j
    rw [hh.1, pair_f hh hf hef, (hW w hw j).2, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right ((map_ne_zero s).2 hd)
  have h0 : pairMap e f (a, b) = 0 := by
    rw [pairMap_apply]
    simp [ha, hb]
  rw [h0, zero_add]
  exact hw

theorem extend_isom [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (U : Submodule L V) (φ : U →ₗ[L] V) (hinj : Function.Injective φ)
    (hiso : ∀ x y : U, h (φ x) (φ y) = h x y) :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ ∀ x : U, g x = φ x := by
  letI : StarRing L :=
    { star := s
      star_involutive := hs
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add s }
  have hadd : ∀ x y z, h (x + y) z = h x z + h y z := fun x y z => by
    rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]
  have hsm : ∀ (c : L) x z, h (c • x) z = s c * h x z := fun c x z => by
    rw [hh.2.2.1 z (c • x), hh.2.1, map_mul, ← hh.2.2.1]
  let B : V →ₗ⋆[L] V →ₗ[L] L := LinearMap.mk₂'ₛₗ (starRingEnd L) (RingHom.id L) h hadd
    (fun c x z => hsm c x z) hh.1 (fun c x z => hh.2.1 c x z)
  have hB : ∀ x y, B x y = h x y := fun _ _ => rfl
  obtain ⟨g, hg, hgφ⟩ := witt_extension_theorem L V B
    (fun x y => (hh.2.2.1 x y).symm) (fun x hx => hh.2.2.2 x hx) U φ hinj hiso
  exact ⟨g, hg, hgφ⟩

theorem exists_isom [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (hd : δ ≠ 0) {l' : ℕ} (hl : l ≤ l') {e f : Fin l → V} {W : Submodule L V}
    {e' f' : Fin l' → V} {W' : Submodule L V}
    (F : IsFrame h δ e f W) (F' : IsFrame h δ e' f' W') :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ (∀ i, g (e i) = e' (Fin.castLE hl i)) ∧
      ∀ i, g (f i) = f' (Fin.castLE hl i) := by
  obtain ⟨he, hf, hef, -, -, -⟩ := F
  obtain ⟨he', hf', hef', -, -, -⟩ := F'
  have hι : Function.Injective (Fin.castLE hl) := Fin.castLE_injective hl
  have he2 : ∀ i j, h (e' (Fin.castLE hl i)) (e' (Fin.castLE hl j)) = 0 := fun i j => he' _ _
  have hf2 : ∀ i j, h (f' (Fin.castLE hl i)) (f' (Fin.castLE hl j)) = 0 := fun i j => hf' _ _
  have hef2 : ∀ i j, h (e' (Fin.castLE hl i)) (f' (Fin.castLE hl j)) = if i = j then δ else 0 := by
    intro i j
    rw [hef']
    simp only [hι.eq_iff]
  have Tinj := pairMap_injective hh hd he hf hef
  have T'inj := pairMap_injective (e := fun i => e' (Fin.castLE hl i))
    (f := fun i => f' (Fin.castLE hl i)) hh hd he2 hf2 hef2
  let T : ((Fin l → L) × (Fin l → L)) →ₗ[L] V := pairMap e f
  let T' : ((Fin l → L) × (Fin l → L)) →ₗ[L] V :=
    pairMap (fun i => e' (Fin.castLE hl i)) (fun i => f' (Fin.castLE hl i))
  let E := LinearEquiv.ofInjective T Tinj
  have hφE : ∀ p, (T' ∘ₗ E.symm.toLinearMap) (E p) = T' p := fun p => by simp
  have hEv : ∀ p, ((E p : LinearMap.range T) : V) = T p := fun p => rfl
  obtain ⟨g, hg, hgφ⟩ := extend_isom hs hh (LinearMap.range T) (T' ∘ₗ E.symm.toLinearMap)
    (T'inj.comp E.symm.injective) (by
      intro x y
      obtain ⟨p, rfl⟩ := E.surjective x
      obtain ⟨r, rfl⟩ := E.surjective y
      rw [hφE, hφE, hEv, hEv]
      exact (pair_form hh he2 hf2 hef2 p r).trans (pair_form hh he hf hef p r).symm)
  have hgT : ∀ p, g (T p) = T' p := fun p => by
    have := hgφ (E p)
    rwa [hφE, hEv] at this
  refine ⟨g, hg, fun i => ?_, fun i => ?_⟩
  · have := hgT (Pi.single i 1, 0)
    simpa [T, T', pairMap_apply, Pi.single_apply] using this
  · have := hgT (0, Pi.single i 1)
    simpa [T, T', pairMap_apply, Pi.single_apply] using this

theorem frame_core [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (hd : δ ≠ 0) {l' : ℕ} (hl : l ≤ l') {e f : Fin l → V} {W : Submodule L V}
    {e' f' : Fin l' → V} {W' : Submodule L V}
    (F : IsFrame h δ e f W) (F' : IsFrame h δ e' f' W') :
    ∃ (q : Fin l ≃ Fin l') (g : V ≃ₗ[L] V), IsIso h g ∧ (∀ i, g (e i) = e' (q i)) ∧
      (∀ i, g (f i) = f' (q i)) ∧ ∀ w, w ∈ W ↔ g w ∈ W' := by
  obtain ⟨g, hg, ge, gf⟩ := exists_isom hs hh hd hl F F'
  have hmove : ∀ y x, h y (g.symm x) = h (g y) x := fun y x => by
    have := hg y (g.symm x)
    simpa using this.symm
  have heq : l = l' := by
    by_contra hne
    have hlt : l < l' := lt_of_le_of_ne hl hne
    let j : Fin l' := ⟨l, hlt⟩
    have hj : ∀ i : Fin l, j ≠ Fin.castLE hl i := fun i hji => by
      have := congrArg Fin.val hji
      simp [j] at this
      omega
    have hx : g.symm (e' j) ∈ W := by
      refine mem_of_perp hh hd F _ (fun i => ?_) (fun i => ?_)
      · rw [hmove, ge]
        exact F'.1 _ _
      · rw [hmove, gf, hh.2.2.1 (e' j), F'.2.2.1, if_neg (hj i), map_zero]
    have h0 : g.symm (e' j) = 0 := by
      refine F.2.2.2.2.1 _ hx ?_
      rw [hmove]
      simpa using F'.1 j j
    have he0 : e' j = 0 := by simpa using h0
    have := F'.2.2.1 j j
    rw [he0, h_zero_left hh, if_pos rfl] at this
    exact hd this.symm
  subst heq
  refine ⟨Equiv.refl _, g, hg, fun i => ge i, fun i => gf i, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · refine mem_of_perp hh hd F' _ (fun i => ?_) (fun i => ?_)
    · have := ge i
      have hi : e' i = g (e i) := this.symm
      rw [hi, hg]
      exact (F.2.2.2.1 w hw i).1
    · have := gf i
      have hi : f' i = g (f i) := this.symm
      rw [hi, hg]
      exact (F.2.2.2.1 w hw i).2
  · refine mem_of_perp hh hd F _ (fun i => ?_) (fun i => ?_)
    · rw [← hg, show g (e i) = e' i from ge i]
      exact (F'.2.2.2.1 _ hw i).1
    · rw [← hg, show g (f i) = f' i from gf i]
      exact (F'.2.2.2.1 _ hw i).2

theorem stWitt : StWitt := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l l' e f W e' f' W' F F'
  rcases le_total l l' with hl | hl
  · exact frame_core hs.1 hh hδ.1 hl F F'
  · obtain ⟨q, g, hg, ge, gf, hw⟩ := frame_core hs.1 hh hδ.1 hl F' F
    refine ⟨q.symm, g.symm, fun x y => ?_, fun i => ?_, fun i => ?_, fun w => ?_⟩
    · have := hg (g.symm x) (g.symm y)
      simpa using this.symm
    · rw [LinearEquiv.symm_apply_eq, ge, q.apply_symm_apply]
    · rw [LinearEquiv.symm_apply_eq, gf, q.apply_symm_apply]
    · simpa using (hw (g.symm w)).symm

end GlobalTheory.CompanionTheory.FlWitt

end
end

