import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailCone
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.CoeffPsiMulSingle

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotientAdditivity

theorem altSum_eq {k : Type u} [Field k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, FiniteDimensional k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, FiniteDimensional k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, FiniteDimensional k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (h0 : Function.Injective (f 0)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i)) (hδf : ∀ i, Function.Exact (δ i) (f (i + 1))) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) =
      (-1 : ℤ) ^ M * Module.finrank k (LinearMap.range (δ M)) := by
  have hB : ∀ i, (Module.finrank k (B i) : ℤ) =
      Module.finrank k (LinearMap.range (f i)) + Module.finrank k (LinearMap.range (g i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (g i), LinearMap.exact_iff.1 (hfg i)]
    push_cast; ring
  have hC : ∀ i, (Module.finrank k (C i) : ℤ) =
      Module.finrank k (LinearMap.range (g i)) + Module.finrank k (LinearMap.range (δ i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (δ i), LinearMap.exact_iff.1 (hgδ i)]
    push_cast; ring
  have hA : ∀ i, (Module.finrank k (A (i + 1)) : ℤ) =
      Module.finrank k (LinearMap.range (δ i)) + Module.finrank k (LinearMap.range (f (i + 1))) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (f (i + 1)), LinearMap.exact_iff.1 (hδf i)]
    push_cast; ring
  have hA0 : (Module.finrank k (A 0) : ℤ) = Module.finrank k (LinearMap.range (f 0)) := by
    rw [← LinearMap.finrank_range_add_finrank_ker (f 0), LinearMap.ker_eq_bot.2 h0, finrank_bot]
    simp
  induction M with
  | zero => rw [Finset.sum_range_one, hA0, hB 0, hC 0]; ring
  | succ M ih => rw [Finset.sum_range_succ, ih, hA M, hB (M + 1), hC (M + 1)]; ring

section Top

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

theorem cdeg_top (i : ℕ) : Cech.Cdeg G (fun _ => (⊤ : Submodule R _)) i = ⊤ := by
  ext s; simp [Cech.Cdeg]

theorem cocyDeg_top (i : ℕ) : Cech.cocyDeg G (fun _ => ⊤) ρ i = LinearMap.ker (Cech.d G ρ i) := by
  rw [Cech.cocyDeg, cdeg_top, inf_top_eq]

theorem bdryDeg_top (i : ℕ) : Cech.bdryDeg G (fun _ => ⊤) ρ i = Cech.bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i => rw [Cech.bdryDeg, Cech.bdry, cdeg_top, Submodule.map_top]

def hdegTopEquiv (i : ℕ) : Cech.Hdeg G (fun _ => ⊤) ρ i ≃ₗ[R] Cech.H G ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i)) (by
    ext z
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [bdryDeg_top] at hy
      exact hy
    · intro hz
      refine ⟨⟨z.1, (cocyDeg_top G ρ i).symm ▸ z.2⟩, ?_, rfl⟩
      rw [bdryDeg_top]; exact hz)

theorem hdeg_subsingleton {R' : Type*} [CommRing R'] [∀ I, Module R' (G I)] (deg : ∀ I, Submodule R' (G I))
    (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R'] G J) (i : ℕ) [IsEmpty (Cech.Idx U i)] :
    Subsingleton (Cech.Hdeg G deg ρ' i) := by
  have : Subsingleton (Cech.cocyDeg G deg ρ' i) :=
    ⟨fun a b => Subtype.ext (funext fun I => isEmptyElim I)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, rfl⟩ := Cech.Hdeg_mk_surjective a
  obtain ⟨z', rfl⟩ := Cech.Hdeg_mk_surjective b
  rw [Subsingleton.elim z z']

end Top

theorem idx_isEmpty {Ω : Type w} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) : IsEmpty (Cech.Idx (support x) (N + 1)) :=
  ⟨fun I => by
    have h1 := Finset.card_le_card I.1.2.2
    have h2 := Finset.card_le_univ (support x)
    have h3 := I.2
    simp only [Fintype.card_fin] at h2
    omega⟩

section Quot

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    (F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :=
  (SubSystem.quotSub F₂ F₃ I).mapQ (SubSystem.quotSub F₁ F₃ I)
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (fun _ hy => hy)

def quotPr (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) →ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₃ I).mapQ (SubSystem.quotSub F₁ F₂ I) LinearMap.id (by intro _ hy; exact h32 I hy)

theorem quotRes_comp (F₁ F₂ : SubSystem k x E) (I J K : Chart x) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (SubSystem.quotRes F₁ F₂ J K hJK).comp (SubSystem.quotRes F₁ F₂ I J hIJ) =
      SubSystem.quotRes F₁ F₂ I K (hIJ.trans hJK) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem quotInl_comm (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotInl F₁ F₂ F₃ h21 J (SubSystem.quotRes F₂ F₃ I J h m) =
      SubSystem.quotRes F₁ F₃ I J h (quotInl F₁ F₂ F₃ h21 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl

theorem quotPr_comm (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :
    quotPr F₁ F₂ F₃ h32 J (SubSystem.quotRes F₁ F₃ I J h m) =
      SubSystem.quotRes F₁ F₂ I J h (quotPr F₁ F₂ F₃ h32 I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m; rfl

theorem quotInl_injective (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    Function.Injective (quotInl F₁ F₂ F₃ h21 I) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) :
      F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact h'

theorem quotPr_quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotPr F₁ F₂ F₃ h32 I (quotInl F₁ F₂ F₃ h21 I m) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (⟨(y : E), h21 I y.2⟩ : F₁.sub I) : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact y.2

theorem exists_quotInl (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I)
    (hm : quotPr F₁ F₂ F₃ h32 I m = 0) : ∃ y, quotInl F₁ F₂ F₃ h21 I y = m := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h' : (Submodule.Quotient.mk z : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) = 0 := hm
  rw [Submodule.Quotient.mk_eq_zero] at h'
  exact ⟨Submodule.Quotient.mk ⟨z, h'⟩, rfl⟩

theorem quotPr_surjective (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    Function.Surjective (quotPr F₁ F₂ F₃ h32 I) := by
  intro m
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact ⟨Submodule.Quotient.mk z, rfl⟩

theorem finrank_quotH (F₁ F₂ : SubSystem k x E) (i : ℕ) :
    Module.finrank k (SubSystem.quotH F₁ F₂ i) =
      Module.finrank k (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (fun _ => ⊤)
        (SubSystem.quotRes F₁ F₂) i) :=
  (hdegTopEquiv _ _ i).finrank_eq.symm

end Quot

end SnapperQuotientAdditivity

set_option maxHeartbeats 1000000 in
open SnapperQuotientAdditivity in

theorem SnapperQuotAdd.proof (hfin : SnapperSubquotFinite.Statement.{u, v, w}) :
    SnapperQuotAdd.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ hfg h21 h32
  have h31 : ∀ I, F₃.sub I ≤ F₁.sub I := fun I => (h32 I).trans (h21 I)
  have hdd := CechDSq.proof (N + 1) (support x) k
    (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem) (quotRes_comp F₁.toSubSystem F₃.toSubSystem)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (B := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem)
    (ρB := SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := quotInl F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h21)
    (ψ := quotPr F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h32)
  have L1 := L (quotInl_comm _ _ _ h21)
  have L2 := L1 (quotPr_comm _ _ _ h32)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (quotInl_injective _ _ _ h21)
  have L5 := L4 (quotPr_quotInl _ _ _ h21 h32)
  have L6 := L5 (fun I m _ hm => (exists_quotInl _ _ _ h21 h32 I m hm).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L7 := L6 (fun I m _ => (quotPr_surjective _ _ _ h32 I m).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  have h0 := liftZP_newton.1
  have hex := liftZP_newton.2
  choose δ hgδ hδf using fun i => (hex i).2
  have fin : ∀ (G₁ G₂ : SubFamily k x E), (∀ I, G₁.sub I ≤ F₁.sub I) → (∀ I, G₂.sub I ≤ G₁.sub I) → ∀ i,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (fun _ => ⊤) (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := by
    intro G₁ G₂ h1 h2 i
    have : FiniteDimensional k (Cech.H (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := hfin k Ω N x E F₁ G₁ G₂ hfg h1 h2 i
    exact (hdegTopEquiv _ _ i).symm.finiteDimensional
  have := fin F₂ F₃ h21 h32
  have := fin F₁ F₃ (fun _ => le_rfl) h31
  have := fin F₁ F₂ (fun _ => le_rfl) h21
  have key := altSum_eq _ _ _ _ _ δ h0 (fun i => (hex i).1) hgδ hδf N
  have := idx_isEmpty x
  have hsub := hdeg_subsingleton (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)
  have hδN : Module.finrank k (LinearMap.range (δ N)) = 0 := by
    have hz : Module.finrank k (Cech.Hdeg (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact Nat.eq_zero_of_le_zero ((Submodule.finrank_le (LinearMap.range (δ N))).trans hz.le)
  rw [hδN] at key
  simp only [Nat.cast_zero, mul_zero, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  simp only [eulerCharQuot, finrank_quotH]
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem aeval_ne_zero_of_mem_monos_support {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

theorem isUnit_coneLaurent_of_mem_monos {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : IsUnit (coneLaurent S x s) := by
  obtain ⟨e, he⟩ := monos_isHomogeneous hs
  rw [coneLaurent_of_isHomogeneous he]
  exact isUnit_coneSingle (S := S) (x := x) e (aeval_ne_zero_of_mem_monos_support hI hs)

variable (M : FinGradedSub (S := S) (x := x) Ω)

def locCone (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSub I →ₗ[Poly S N] ConeLaurent S x :=
  LocalizedModule.lift (monos I) M.coneSub.subtype fun s => by
    rw [Module.End.isUnit_iff]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp (isUnit_coneLaurent_of_mem_monos hI s.2)

theorem locCone_mk (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSub)
    (s : monos (S := S) I) :
    coneLaurent S x s * locCone M I hI (LocalizedModule.mk m s) = m := by
  have h1 : (s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s m
  have h2 : locCone M I hI ((s : Poly S N) • LocalizedModule.mk m s) = m := by
    change LocalizedModule.lift (monos I) M.coneSub.subtype _
      ((s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub)) = m
    rw [h1]
    simp
  have h3 := (locCone M I hI).map_smul (s : Poly S N) (LocalizedModule.mk m s : LocMod S N M.coneSub I)
  exact h3.symm.trans h2

theorem locCone_mk_eq {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSub}
    {s : monos (S := S) I} {w : ConeLaurent S x} (h : coneLaurent S x s * w = m) :
    locCone M I hI (LocalizedModule.mk m s) = w :=
  (isUnit_coneLaurent_of_mem_monos hI s.2).mul_left_cancel ((locCone_mk M I hI m s).trans h.symm)

theorem locCone_injective (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locCone M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => locCone M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locCone_mk M I hI m s
  rw [hz, mul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]

theorem locCone_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSub I) :
    locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub =>
      locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locCone_mk_eq M hJ (locCone_mk M I _ m s)

theorem locMod_subsingleton {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSub I) := by
  have hX : ∀ m : M.coneSub, (X i : Poly S N) • m = 0 := fun m => by
    apply Subtype.ext
    change coneLaurent S x (X i) * (m : ConeLaurent S x) = 0
    rw [coneLaurent_of_isHomogeneous (isHomogeneous_X S i), aeval_X, hx, AddMonoidAlgebra.single_zero,
      map_zero, zero_mul]
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => z = 0) (fun m s => ?_) z
  rw [← LocalizedModule.mk_cancel_common_left ⟨X i, X_mem_monos hi⟩ s m]
  have h0 : (⟨X i, X_mem_monos hi⟩ : monos (S := S) I) • m = 0 := hX m
  rw [h0, LocalizedModule.zero_mk]

theorem locCone_degLoc (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSub I.1}
    (hz : z ∈ degLoc M.coneGraded c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locCone M I.1 hI z = coneSingle S x c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locCone M I.1 hI z = coneSingle S x c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffAt S x a (m : ConeLaurent S x),
      Submodule.subset_span ⟨coeffAt S x a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locCone_mk_eq M hI ?_⟩
    rw [← coneLaurent_smul, smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0,
      show c + (e : ℤ) = a by omega]
    exact (M.eq_coneSingle_of_mem_conePiece hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add, map_add, hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    exact ⟨s • v, (M.tilde c _).smul_of_tower_mem s hv, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩

def tildeGens (c : ℤ) (I : Chart x) : Set Ω :=
  {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}

theorem tilde_le_span (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set Ω) ⊆ Submodule.span S (tildeGens M c I) := by
  have hclosed : ∀ a : chartRing S x I, ∀ y ∈ Submodule.span S (tildeGens M c I),
      a • y ∈ Submodule.span S (tildeGens M c I) := by
    intro a y hy
    refine Submodule.span_induction (p := fun y _ => a • y ∈ Submodule.span S (tildeGens M c I))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
      obtain ⟨f, s', e', hs', hf, hse', ha⟩ := a.2
      refine Submodule.subset_span ⟨aeval x f • m, s' * s, b + e', e' + e, mul_mem hs' hs, hse'.mul hse,
        M.smul_mem e' b f m hf hm, by push_cast; omega, ?_⟩
      simp only [chartRing_smul_def, smul_eq_mul, ha, map_mul, mul_inv, div_eq_mul_inv]
      ring
    · rw [smul_zero]; exact zero_mem _
    · intro y y' _ _ hy hy'; rw [smul_add]; exact add_mem hy hy'
    · intro t y _ hy
      have : a • (t • y) = t • (a • y) := by
        rw [chartRing_smul_def, chartRing_smul_def, Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]; exact Submodule.smul_mem _ t hy
  intro y hy
  exact Submodule.span_induction (p := fun y _ => y ∈ Submodule.span S (tildeGens M c I))
    (fun y hy => Submodule.subset_span hy) (zero_mem _) (fun _ _ _ _ => add_mem)
    (fun a y _ hy => hclosed a y hy) hy

theorem exists_locCone_eq (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : Ω}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGraded c I, locCone M I.1 hI z = coneSingle S x c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGraded c I,
    locCone M I.1 hI z = coneSingle S x c y) ?_ ?_ ?_ ?_ (tilde_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨coneSingle S x a m, M.coneSingle_mem_coneSub hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.coneSingle_mem_conePiece hm, hse, hae, rfl⟩,
      locCone_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • coneSingle S x c ((aeval x s)⁻¹ • m) = coneSingle S x a m
    rw [smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add, map_add, hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩

end Loc

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra TwistFin

universe u w

theorem TwistFinite.proof (hE : Extension.Statement.{u, w, w}) (hSF : SerreFinite.Statement.{u, w}) :
    TwistFinite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hx _ hgen
  classical
  obtain ⟨M0, -, hG⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨n0, d0, g0, -, hspan⟩ := M0.fg
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hfin : Module.Finite (Sy S r) (cohom (tgraded x η S n0 d0 g0) 0 0) :=
    hSF (Sy S r) N _ (tgraded x η S n0 d0 g0) inferInstance 0 0
  let Γ : Set (Amb x η) := {γ | ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
    γ = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s)}
  have hΓ : Γ ⊆ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
    rintro _ ⟨b, s, hs, rfl⟩
    refine mem_range_readChartH0 x η S n0 d0 g0 i0 hi0 _ fun I hI => ?_
    refine chart_pre x η S M0 G B hgen hG hspan I hI b ?_
    rw [SubSystem.secs, Submodule.mem_iInf] at hs
    exact hs (toChart x I hI)
  have hfg : (Submodule.span (Sy S r) Γ).FG := by
    have : IsNoetherian (Sy S r) (LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0)) :=
      isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp inferInstance)
    exact isNoetherian_submodule.mp this _ (Submodule.span_le.mpr hΓ)
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨T, hTΓ, htT⟩ := Submodule.subset_span_finite_of_subset_span
    (R := Sy S r) (s := Γ) (t := t) (by rw [← ht]; exact Submodule.subset_span)
  have hle : Submodule.span (Sy S r) Γ ≤ Submodule.span (Sy S r) (T : Set (Amb x η)) := by
    rw [← ht, Submodule.span_le]
    exact htT
  have hT : ∀ γ : T, ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
      (γ : Amb x η) = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) := fun γ => hTΓ γ.2
  choose bT sT hsT hγT using hT
  let e := T.equivFin
  refine ⟨T.card, fun k => bT (e.symm k), fun k => sT (e.symm k), fun k => hsT _, ?_⟩
  intro b s hs
  have hmem : (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) ∈
      Submodule.span (Sy S r) (T : Set (Amb x η)) :=
    hle (Submodule.subset_span ⟨b, s, hs, rfl⟩)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hmem
  have hcoef := congrArg (fun a => (toA x η a).coeff ((0 : ℤ), (b : ℤ))) hc
  simp only [AddEquiv.apply_symm_apply, map_sum, toA_smulSy, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, coeff_single, Finsupp.single_eq_same] at hcoef
  rw [← hcoef]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h1 : toA x η γ = single ((0 : ℤ), ((bT ⟨γ, hγ⟩ : ℕ) : ℤ)) (sT ⟨γ, hγ⟩) := by
    have := congrArg (toA x η) (hγT ⟨γ, hγ⟩)
    rwa [AddEquiv.apply_symm_apply] at this
  rw [h1, coeff_psi_mul_single]
  refine Submodule.sum_mem _ fun d _ => ?_
  split_ifs with hdb
  · refine Submodule.subset_span ⟨e ⟨γ, hγ⟩, homogeneousComponent d (c γ), d,
      homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact hdb
    · simp only [Equiv.symm_apply_apply]
  · exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

open Classical in

def CycleSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    (∀ G ∈ J.minimalPrimes, ringKrullDim (Poly S N ⧸ G) ≤ 2) →
    ∀ᶠ c : ℕ in atTop,
      interSum J ![M.toSubSystem] c =
        ∑ᶠ G : Ideal (Poly S N),
          if h : G ∈ J.minimalPrimes ∧ IsSubvar x G 1 then
            haveI : G.IsPrime := h.1.1.1
            ((cutMult J G).toNat : ℤ) * interNum G ![M.toSubSystem]
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

