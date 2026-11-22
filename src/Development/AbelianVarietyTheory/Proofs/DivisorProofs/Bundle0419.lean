import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicInductionTrivialPreservesVirtualCharact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursio
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct GlobalTheory.ParabVirt
open scoped Classical

noncomputable section
namespace GlobalTheory.ShinPsiRec

variable {F : Type} [Field F]

def low (a n : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0}
  add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

theorem mem_stab_low_iff (a n : ℕ) (x : GL (Fin n) F) : x ∈ stab (low (F := F) a n) ↔ InPar a x := by
  rw [mem_stab]
  constructor
  · intro h i j hj hi
    have hv : (Pi.single j 1 : Fin n → F) ∈ low a n := by
      intro k hk
      have : k ≠ j := by intro e; subst e; omega
      simp [Pi.single_apply, this]
    have := h _ hv i hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec_single_one] using this
  · intro h v hv i hi
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < a
    · rw [h i j hj hi, zero_mul]
    · rw [hv j (by omega), mul_zero]

def lowEquiv {a n : ℕ} (ha : a ≤ n) : low (F := F) a n ≃ₗ[F] (Fin a → F) where
  toFun v := fun i => v.1 (Fin.castLE ha i)
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun k => if h : (k : ℕ) < a then w ⟨k, h⟩ else 0, fun k hk => dif_neg (by omega)⟩
  left_inv v := by
    ext k
    dsimp only
    split_ifs with h
    · rfl
    · exact (v.2 k (by omega)).symm
  right_inv w := by
    funext i
    simp

theorem resMat_low {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : p ∈ stab (low (F := F) a n)) :
    resMat (low a n) (lowEquiv ha) ⟨p, hp⟩ = tl a (p : Matrix (Fin n) (Fin n) F) := by
  ext i j
  have hs : ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1 = Pi.single (Fin.castLE ha j) 1 := by
    funext k
    change (if h : (k : ℕ) < a then (Pi.single j 1 : Fin a → F) ⟨k, h⟩ else 0) = _
    split_ifs with h
    · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
    · have : k ≠ Fin.castLE ha j := by
        intro e; rw [e, Fin.val_castLE] at h; exact h j.2
      simp [Pi.single_apply, this]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply]
  change (Matrix.toLin' (p : Matrix (Fin n) (Fin n) F) ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1)
    (Fin.castLE ha i) = _
  rw [hs, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, ent, dif_pos (And.intro hi hj), Matrix.transpose_apply]
  rfl

theorem tl_isUnit {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    IsUnit (tl a (p : Matrix (Fin n) (Fin n) F)) := by
  have hp' := (mem_stab_low_iff a n p).2 hp
  rw [← resMat_low ha p hp']
  exact IsUnit.map (resMat (low a n) (lowEquiv ha)) (Group.isUnit _)

theorem coe_tlG {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    ((tlG a p : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p : Matrix (Fin n) (Fin n) F) := by
  unfold tlG toG
  rw [dif_pos (tl_isUnit ha p hp)]
  rfl

theorem psi_restrict_low (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F)
    (hp : p ∈ stab (low (F := F) a n)) :
    psi S (low (F := F) a n) ((Matrix.toLin' (p : Matrix (Fin n) (Fin n) F)).restrict hp) =
      psiG S a (tlG a p) := by
  rw [psiG, coe_tlG ha p ((mem_stab_low_iff a n p).1 hp), ← resMat_low ha p hp]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_toMatrix']
  rw [psi_conj]

def resPsi (S : F[X] → ℂ) {n : ℕ} (x : GL (Fin n) F) (W : Submodule F (Fin n → F)) : ℂ :=
  if h : x ∈ stab W then psi S W ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0

theorem finsum_rank_eq_hc [Finite F] (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (x : GL (Fin n) F) :
    ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  set W₀ := low (F := F) a n with hW₀def
  have hW₀ : Module.finrank F W₀ = a := (lowEquiv ha).finrank_eq.trans (Module.finrank_fin_fun F)
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (lin t).toLinearMap, (LinearEquiv.finrank_map_eq _ _).trans hW₀⟩
  have hs : Function.Surjective π := by
    intro W
    obtain ⟨f⟩ : Nonempty (W₀ ≃ₗ[F] W.1) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hW₀.trans W.2.symm)
    obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
    obtain ⟨t, rfl⟩ := lin_surjective g
    refine ⟨t, Subtype.ext ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      have := (f ⟨v, hv⟩).2
      rw [hg] at this
      exact this
    · exact (π t).2.trans W.2.symm
  have hsum := sum_fibres (stab W₀) π hs
    (fun s t => Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)) (fun W => resPsi S x W.1)
  have hg : ∀ t : GL (Fin n) F, gal (RingHom.id F) n t = t := by
    intro t; ext i j; simp [gal]
  have hterm : ∀ t : GL (Fin n) F, resPsi S x (π t).1 =
      (if InPar a (t⁻¹ * x * gal (RingHom.id F) n t) then
        psiG S a (tlG a (t⁻¹ * x * gal (RingHom.id F) n t)) *
          (fun _ => (1 : ℂ)) (brG a (n - a) (t⁻¹ * x * gal (RingHom.id F) n t)) else 0) := by
    intro t
    rw [hg, mul_one]
    simp only [resPsi, π]
    by_cases h : t⁻¹ * x * t ∈ stab W₀
    · have h' := (conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h', if_pos ((mem_stab_low_iff a n _).1 h), ← psi_restrict_low S ha _ h,
        ← psi_conj F S _ _ ((lin t).submoduleMap W₀)]
      congr 1
      refine LinearMap.ext fun v => ?_
      obtain ⟨w, rfl⟩ := ((lin t).submoduleMap W₀).surjective v
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      ext1
      change lin x (lin t w) = lin t (lin (t⁻¹ * x * t) w)
      rw [← lin_mul, ← lin_mul, mul_assoc, mul_inv_cancel_left]
    · rw [dif_neg (fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')),
        if_neg (fun h'' => h ((mem_stab_low_iff a n _).2 h''))]
  have hcard : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card (stab W₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_stab_low_iff a n p).symm)
  have hc0 : (Nat.card (stab W₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [hc, hcTw]
  rw [hcard, ← finsum_congr hterm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum,
    inv_mul_cancel_left₀ hc0]

end GlobalTheory.ShinPsiRec

namespace GlobalTheory.ShinPsiRec

theorem ne_top_iff_finrank_lt {F : Type} [Field F] {n : ℕ} (W : Submodule F (Fin n → F)) :
    W ≠ ⊤ ↔ Module.finrank F W < n := by
  constructor
  · intro h
    have := Submodule.finrank_lt h
    rwa [Module.finrank_fin_fun] at this
  · intro h htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h
    exact lt_irrefl _ h

theorem psiG_eq_chG_sub_hc (F : Type) [Field F] [Finite F] (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  show psi S _ _ = S _ - _
  rw [psi_eq, Matrix.charpoly_toLin']
  congr 1
  rw [Finset.sum_congr rfl fun a ha =>
    (finsum_rank_eq_hc S (le_of_lt (Finset.mem_range.1 ha)) x).symm]
  have step : ∀ a : ℕ, ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      ∑ W : Submodule F (Fin n → F), if Module.finrank F W = a then resPsi S x W else 0 := by
    intro a
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simp only [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (g := fun W => resPsi S x W.1) fun W _ => by
    unfold resPsi; rw [dif_pos (show x ∈ stab W.1 from W.2.2)]]
  rw [← Finset.sum_subtype (Finset.univ.filter fun W : Submodule F (Fin n → F) => W ≠ ⊤ ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W)
    (fun W => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (resPsi S x), Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hx : ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W
  · simp only [Finset.mem_range, ne_top_iff_finrank_lt, and_iff_left hx]
  · have hx' : x ∉ stab W := hx
    simp [resPsi, hx', hx]

end GlobalTheory.ShinPsiRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityEtaleLocallyPowPrimitiveRoot
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.RootLoc

theorem root_loc_pow_prim : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  intro q _ U hq ω hω
  apply GlobalTheory.EtC.loc_trans
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  have hx : (g.appTop.hom (ω : Γ(U, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hω, Units.val_one, map_one]
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q V).2.2.1 ζ _ hx) ?_
  rintro W k ⟨a, ha⟩
  refine ⟨ζ.map k.appTop.hom, a, ?_⟩
  rw [Units.coe_map]
  exact (PrimLoc.appTop_comp g k _).trans ha

end GlobalTheory.EtC.RootLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorRightOperatorStatement
section
open GlobalTheory.SliceSchwartz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_tensor_right_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  first | exact @GlobalTheory.SliceOp.exists_tensor_clm | exact GlobalTheory.SliceOp.exists_tensor_clm | (intros; apply GlobalTheory.SliceOp.exists_tensor_clm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open scoped TensorProduct

namespace GlobalTheory.EtC.TensLocBij

theorem locAll {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) :
    Loc U P := GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem locMono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem locAnd {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q hP hQ

theorem locTrans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem locFin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

section Alg

variable {S : Type*} [CommRing S] {A B D : Type*} [AddCommGroup A] [Module S A]
  [AddCommGroup B] [Module S B] [AddCommGroup D] [Module S D]

theorem exists_fg_lTensor (x : A ⊗[S] B) :
    ∃ (J : Submodule S B) (_ : J.FG) (y : A ⊗[S] J), x = LinearMap.lTensor A J.subtype y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, 0, by simp⟩
  | tmul a b => exact ⟨S ∙ b, Submodule.fg_span_singleton b,
      a ⊗ₜ[S] ⟨b, Submodule.mem_span_singleton_self _⟩, rfl⟩
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ih₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ih₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂, LinearMap.lTensor A (Submodule.inclusion le_sup_left) y₁ +
      LinearMap.lTensor A (Submodule.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl

theorem rTensor_comm_eq {Y : Type*} [AddCommGroup Y] [Module S Y] (g : B →ₗ[S] Y) (x : A ⊗[S] B) :
    LinearMap.rTensor A g (TensorProduct.comm S A B x) =
      TensorProduct.comm S A Y (LinearMap.lTensor A g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem fg_lTensor_eq_zero {J : Submodule S D} (hJ : J.FG) {t : A ⊗[S] J}
    (h : LinearMap.lTensor A J.subtype t = 0) :
    ∃ (K : Submodule S D) (hJK : J ≤ K), K.FG ∧
      LinearMap.lTensor A (Submodule.inclusion hJK) t = 0 := by
  have h' : LinearMap.rTensor A J.subtype (TensorProduct.comm S A J t) = 0 := by
    rw [rTensor_comm_eq, h, map_zero]
  obtain ⟨K, hJK, hK, h0⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hJ h'
  refine ⟨K, hJK, hK, ?_⟩
  rw [rTensor_comm_eq] at h0
  exact (LinearEquiv.map_eq_zero_iff _).mp h0

end Alg

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem surj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (U : Scheme.{0}) (y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U))) :
    Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x =
      TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y := by
  induction y using TensorProduct.induction_on with
  | zero => exact locAll fun V g => ⟨0, by simp⟩
  | tmul c q =>
    exact locMono (hs U q) fun V g ⟨x, hx⟩ => ⟨(C.map g.op).hom c ⊗ₜ x, by simp [hx]⟩
  | add a b ha hb =>
    exact locMono (locAnd ha hb) fun V g ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ => ⟨x + x', by simp [map_add, hx, hx']⟩

theorem kerPart
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (V : Scheme.{0}) (K : Submodule (ULift.{1} R) (P.obj (op V)))
    (hK : ∀ k ∈ K, (φ.app (op V)).hom k = 0) (z : C.obj (op V) ⊗[ULift.{1} R] K) :
    Loc V fun _ h => TensorProduct.map (C.map h.op).hom (P.map h.op).hom
      (LinearMap.lTensor _ K.subtype z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact locAll fun _ _ => by simp
  | tmul c k => exact locMono (hi V k.1 (hK k.1 k.2)) fun W h hk => by simp [hk]
  | add a b ha hb => exact locMono (locAnd ha hb) fun W h ⟨h1, h2⟩ => by simp [map_add, h1, h2]

theorem map_restr_comp {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) :
    TensorProduct.map (C.map (k ≫ g).op).hom (P.map (k ≫ g).op).hom =
      TensorProduct.map (C.map k.op).hom (P.map k.op).hom ∘ₗ
        TensorProduct.map (C.map g.op).hom (P.map g.op).hom := by
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    TensorProduct.map_comp]

theorem nat_apply {U V : Scheme.{0}} (g : V ⟶ U) (p : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom p) = (Q.map g.op).hom ((φ.app (op U)).hom p) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h p) (φ.naturality g.op)
  simpa using this

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem inj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)))
    (hx : LinearMap.lTensor _ (φ.app (op U)).hom x = 0) :
    Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  obtain ⟨B₀, hB₀, x₀, rfl⟩ := exists_fg_lTensor x
  have hcomp : (B₀.map (φ.app (op U)).hom).subtype ∘ₗ (φ.app (op U)).hom.submoduleMap B₀ =
      (φ.app (op U)).hom ∘ₗ B₀.subtype := rfl
  have ht : LinearMap.lTensor _ (B₀.map (φ.app (op U)).hom).subtype
      (LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) x₀) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨K, hJK, ⟨s, hs'⟩, hK0⟩ := fg_lTensor_eq_zero (hB₀.map _) ht
  have hloc := locFin (ι := Fin s.card)
    (fun i V g => ∃ p, (φ.app (op V)).hom p = (Q.map g.op).hom (s.equivFin.symm i).1)
    (fun i => hs U (s.equivFin.symm i).1)
  apply locTrans
  refine locMono hloc fun V g hV => ?_
  have hle : K ≤ (LinearMap.range (φ.app (op V)).hom).comap (Q.map g.op).hom := by
    rw [← hs', Submodule.span_le]
    intro q hq
    obtain ⟨p, hp⟩ := hV (s.equivFin ⟨q, hq⟩)
    rw [Equiv.symm_apply_apply] at hp
    exact ⟨p, hp⟩
  let ρ := ((Q.map g.op).hom ∘ₗ K.subtype).codRestrict (LinearMap.range (φ.app (op V)).hom)
    (fun k => hle k.2)
  have key : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict ∘ₗ
      TensorProduct.map (C.map g.op).hom (P.map g.op).hom ∘ₗ LinearMap.lTensor _ B₀.subtype =
      TensorProduct.map (C.map g.op).hom ρ ∘ₗ LinearMap.lTensor _ (Submodule.inclusion hJK) ∘ₗ
        LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    simp [ρ, nat_apply]
  have hy : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict
      (TensorProduct.map (C.map g.op).hom (P.map g.op).hom (LinearMap.lTensor _ B₀.subtype x₀)) = 0 := by
    have := congrArg (fun L => L x₀) key
    simp only [LinearMap.comp_apply] at this
    rw [this, hK0, map_zero]
  have hex := lTensor_exact (C.obj (op V))
    (LinearMap.exact_subtype_ker_map (φ.app (op V)).hom.rangeRestrict)
    (LinearMap.surjective_rangeRestrict _)
  obtain ⟨z, hz⟩ := (hex _).mp hy
  have hK : ∀ k ∈ LinearMap.ker (φ.app (op V)).hom.rangeRestrict, (φ.app (op V)).hom k = 0 := by
    intro k hk
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    simpa using this
  refine locMono (kerPart C P Q φ hi V _ hK z) fun W k hk => ?_
  rw [map_restr_comp, LinearMap.comp_apply, ← hz]
  exact hk

theorem main : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  fun _ _ C P Q φ hs hi U => ⟨surj C P Q φ hs U, inj C P Q φ hs hi U⟩

end GlobalTheory.EtC.TensLocBij

theorem GlobalTheory.EtC.tensor_loc_bij : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  GlobalTheory.EtC.TensLocBij.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.OpComp

theorem ev_comp_ofHom' {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (u : I ⟶ K) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x = Sec.map (u.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

def invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat g s a := by
    apply (hb _ s).1
    change ρ.app _ s (Sec.res g ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm a)) =
      ρ.app _ s ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm (Sec.res g a))
    rw [← ρ.nat]
    have e1 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply (Sec.res g a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]
  comm U s t a := by
    apply (hb U t).1
    change ρ.app U t (Sec.map (I.d s t) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)) =
      ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a))
    rw [← ρ.comm]
    have e1 := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply (Sec.map (J.d s t) a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]

theorem invSemi_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invSemi ρ hb).app U s (ρ.app U s a) = a := by
  change (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm (AddEquiv.ofBijective (ρ.app U s) (hb U s) a) = a
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

theorem app_invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (b : Sec (J.X s) U) :
    ρ.app U s ((invSemi ρ hb).app U s b) = b := by
  change AddEquiv.ofBijective (ρ.app U s) (hb U s) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm b) = b
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply b

theorem op_comp_bij : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  intro S R _ _ I J J' ρ ρ' u hu
  refine ⟨fun E n x => ?_, fun hb E n => ?_⟩
  · obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := ρ.image_exists E n α
    rw [ρ.op_spec E n α β hβ]
    change _ = CohomologyClass.mk (zcomp β (Cocycle.ofHom u) (add_zero n))
    refine ρ'.op_spec E n α _ (fun p s h U y => ?_)
    change ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom', hβ, hu]
  · set σ := invSemi ρ hb
    have h1 : ∀ x, σ.op.app E n (ρ.op.app E n x) = x := by
      intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := ρ.image_exists E n α
      rw [ρ.op_spec E n α β hβ]
      refine σ.op_spec E n β α (fun p s h U y => ?_)
      rw [hβ, invSemi_app]
    have h2 : ∀ y, ρ.op.app E n (σ.op.app E n y) = y := by
      intro y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      obtain ⟨α, hα⟩ := σ.image_exists E n β
      rw [σ.op_spec E n β α hα]
      refine ρ.op_spec E n α β (fun p s h U y => ?_)
      rw [hα, app_invSemi]
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end GlobalTheory.EtC.OpComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafSectionEqZeroAtStageOfFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafSection_eq_zero_at_stage_of_filtered_colimit : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  first | (exact @GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero) | (exact GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero) | (intros; apply GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero  <;> assumption)
end

