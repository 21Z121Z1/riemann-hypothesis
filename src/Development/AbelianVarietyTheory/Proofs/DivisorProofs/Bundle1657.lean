import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTower
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilPhi

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory GlobalTheory.PDivGroup GlobalTheory.CartierDual

section Level

variable {O : Type} [CommRing O] {A B : Type} [CommRing A] [CommRing B]

section Alg

variable [Algebra O A] [Algebra O B]

def ev (y : A →ₐ[O] O) (x : B →ₐ[O] O) : A ⊗[O] B →ₐ[O] O :=
  Algebra.TensorProduct.lift y x fun _ _ => Commute.all _ _

@[simp] theorem ev_tmul (y : A →ₐ[O] O) (x : B →ₐ[O] O) (a : A) (b : B) :
    ev y x (a ⊗ₜ b) = y a * x b := rfl

theorem ev_comp_left (y : A →ₐ[O] O) (x : B →ₐ[O] O) :
    (ev y x).comp Algebra.TensorProduct.includeLeft = y := AlgHom.ext fun a => by simp

theorem ev_comp_right (y : A →ₐ[O] O) (x : B →ₐ[O] O) :
    (ev y x).comp Algebra.TensorProduct.includeRight = x := AlgHom.ext fun a => by simp

theorem exists_ev (ψ : A ⊗[O] B →ₐ[O] O) : ∃ y x, ψ = ev y x :=
  ⟨ψ.comp Algebra.TensorProduct.includeLeft, ψ.comp Algebra.TensorProduct.includeRight, by
    ext a <;> simp [← Algebra.TensorProduct.one_def]⟩

def slice (u : A ⊗[O] B) (x : B →ₐ[O] O) : A := tensorToHom O A B u (toConv x.toLinearMap)

def contr (u : A ⊗[O] B) : CartierDual O A →ₗ[O] B :=
  tensorToHom O B A (TensorProduct.comm O A B u)

theorem apply_slice (u : A ⊗[O] B) (y : A →ₐ[O] O) (x : B →ₐ[O] O) :
    y (slice u x) = ev y x u := by
  unfold slice
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp [mul_comm]

theorem apply_contr (u : A ⊗[O] B) (f : CartierDual O A) (x : B →ₐ[O] O) :
    x (contr u f) = f (slice u x) := by
  unfold slice contr
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp [mul_comm]

theorem ev_map_contr (u : A ⊗[O] B) (x x' : B →ₐ[O] O) (t : CartierDual O A ⊗[O] CartierDual O A) :
    ev x x' (TensorProduct.map (contr u) (contr u) t) = pair O A A t (slice u x ⊗ₜ slice u x') := by
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp [apply_contr]

end Alg

variable [HopfAlgebra O A] [Module.Finite O A] [Module.Projective O A]

theorem conv_apply (x y : WithConv (A →ₐ[O] O)) (a : A) :
    (x * y).ofConv a = ev x.ofConv y.ofConv (comul a) := AlgHom.convMul_apply x y a

structure IsBimul (u : A ⊗[O] A) : Prop where
  one_left : ∀ x : A →ₐ[O] O, ev (1 : WithConv (A →ₐ[O] O)).ofConv x u = 1
  one_right : ∀ x : A →ₐ[O] O, ev x (1 : WithConv (A →ₐ[O] O)).ofConv u = 1
  mul_left : ∀ (y y' : WithConv (A →ₐ[O] O)) (x : A →ₐ[O] O),
    ev (y * y').ofConv x u = ev y.ofConv x u * ev y'.ofConv x u
  mul_right : ∀ (y y' : WithConv (A →ₐ[O] O)) (x : A →ₐ[O] O),
    ev x (y * y').ofConv u = ev x y.ofConv u * ev x y'.ofConv u

variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C]
  {u : A ⊗[O] A} (h : IsBimul u)

include C h

theorem isGroupLikeElem_slice (x : A →ₐ[O] O) : IsGroupLikeElem O (slice u x) where
  counit_eq_one := by
    have := h.one_left x
    rw [← apply_slice] at this
    exact this
  comul_eq_tmul_self := TateFree.eq_of_forall_pts O C (A ⊗[O] A) fun ψ => by
    obtain ⟨y, y', rfl⟩ := exists_ev ψ
    have := h.mul_left (toConv y) (toConv y') x
    rw [← apply_slice, conv_apply] at this
    rw [ev_tmul, apply_slice, apply_slice]
    exact this

theorem slice_one : slice u (1 : WithConv (A →ₐ[O] O)).ofConv = 1 :=
  TateFree.eq_of_forall_pts O C A fun y => by rw [apply_slice, h.one_right, map_one]

theorem slice_mul (x x' : WithConv (A →ₐ[O] O)) :
    slice u (x * x').ofConv = slice u x.ofConv * slice u x'.ofConv :=
  TateFree.eq_of_forall_pts O C A fun y => by
    rw [apply_slice, h.mul_right, map_mul, apply_slice, apply_slice]

def contrHom : CartierDual O A →ₐc[O] A where
  __ := contr u
  counit_comp := LinearMap.ext fun f => by
    have := apply_contr u f (1 : WithConv (A →ₐ[O] O)).ofConv
    rw [slice_one C h] at this
    exact this
  map_comp_comul := LinearMap.ext fun f => TateFree.eq_of_forall_pts O C (A ⊗[O] A) fun ψ => by
    obtain ⟨x, x', rfl⟩ := exists_ev ψ
    have := apply_contr u f (toConv x * toConv x').ofConv
    rw [slice_mul C h, conv_apply, ← pair_comul_tmul, ← ev_map_contr] at this
    exact this.symm
  map_one' := TateFree.eq_of_forall_pts O C A fun x => by
    change x (contr u 1) = _
    rw [apply_contr, map_one]
    exact (isGroupLikeElem_slice C h x).counit_eq_one
  map_mul' f g := TateFree.eq_of_forall_pts O C A fun x => by
    change x (contr u (f * g)) = x (contr u f * contr u g)
    rw [map_mul x, apply_contr, apply_contr, apply_contr, mul_apply,
      (isGroupLikeElem_slice C h x).comul_eq_tmul_self, pair_tmul_tmul]

end Level

theorem exists_hom_dual {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
    [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C] (G : PDivGroup p O)
    (u : ∀ n, G.A n ⊗[O] G.A n) (h : ∀ n, IsBimul (u n))
    (hl : ∀ (n : ℕ) (y : G.A (n + 1) →ₐ[O] O) (x : G.A n →ₐ[O] O),
      ev y (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)) (u (n + 1)) =
        ev (y.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1))) x (u n)) :
    ∃ φ : G ⟶ G.dual, ∀ (s s' : G.Tate) (n : ℕ),
      muRoot (pairing G O s (tateMap G G.dual O φ s')) n = ev (s.pt n) (s'.pt n) (u n) := by
  have key : ∀ (n : ℕ) (x : G.A n →ₐ[O] O),
      slice (u (n + 1)) (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)) = G.mulP n (slice (u n) x) :=
    fun n x => TateFree.eq_of_forall_pts O C _ fun y => by
      rw [apply_slice, hl, ← apply_slice]
      rfl
  refine ⟨⟨fun n => contrHom C (h n), fun n => BialgHom.ext fun f =>
    TateFree.eq_of_forall_pts O C _ fun x => ?_⟩, fun s s' n => ?_⟩
  · have h1 := apply_contr (u (n + 1)) f (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n))
    rw [key] at h1
    exact h1.trans (apply_contr (u n) (CartierDual.map (G.mulP n) f) x).symm
  · rw [muRoot_pairing, ← apply_slice]
    congr 1
    refine eq_of_forall_apply (R := O) fun f => ?_
    rw [apply_charElem, ← apply_contr]
    rfl

end GlobalTheory.WeilPhi

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.WeilPhi

open scoped NNReal

attribute [local instance] Over.cartesianMonoidalCategory

section Weil

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {A : Out.PolAV (Sp C)} {k : ℕ}

theorem weil_mul_swap (hk : 1 ≤ k) {x y : Pts A.A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    weil A k x y * weil A k y x = 1 := by
  have hxy : (x * y) ^ k = 1 := by rw [mul_pow, hx, hy, _root_.mul_one]
  have h := weil_self hk hxy
  rw [weil_mul_left hk hx hy hxy, weil_mul_right hk hx hy hx, weil_mul_right hk hx hy hy,
    weil_self hk hx, weil_self hk hy, _root_.one_mul, _root_.mul_one] at h
  exact h

theorem weil_level_left (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) {z s : Pts A.A} (hz : z ^ k = 1)
    (hs : s ^ (k * l) = 1) : weil A (k * l) s z = weil A k (s ^ l) z := by
  have hz' : z ^ (k * l) = 1 := by rw [pow_mul, hz, one_pow]
  have hs' : (s ^ l) ^ k = 1 := by rw [← pow_mul, mul_comm, hs]
  have h1 := weil_mul_swap (Nat.mul_pos hk hl) hz' hs
  rw [weil_level hk hl hz hs] at h1
  exact mul_left_cancel (h1.trans (weil_mul_swap hk hz hs').symm)

end Weil

theorem exists_hom_weil : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralFinite P → ∀ (G : PDivGroup p O) (tw : G.TorsionTower P.Gt), ∃ φ : G ⟶ G.dual, ∀ (s s' : G.Tate) (n : ℕ), algebraMap O C (muRoot (pairing G O s (tateMap G G.dual O φ s')) n) = (weil P.A (p ^ n) (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n)) (P.toA (GlobalTheory.DeRham.spOver (s'.pt n) ≫ tw.y n)) : C) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hW G tw
  have hi : Function.Injective (algebraMap O C) := P.integers.hom_inj
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hi, fun hx => P.integers.exists_of_le_one (P.integers.mem_of_integral hx)⟩
  let q : ∀ n, WithConv (G.A n →ₐ[O] O) →* Pts P.A.A := fun n => P.toA.comp (tw.pts n O)
  have hq : ∀ n x, q n x ^ p ^ n = 1 := fun n x => by rw [← map_pow, G.pts_pow_self, map_one]
  have hp := one_le_ppow p
  have hu : ∀ n, ∃ u : G.A n ⊗[O] G.A n, ∀ y x : WithConv (G.A n →ₐ[O] O),
      algebraMap O C (ev y.ofConv x.ofConv u) = (weil P.A (p ^ n) (q n y) (q n x) : C) := fun n => by
    obtain ⟨u, hu⟩ := hW (G.A n ⊗[O] G.A n) (p ^ n) (hp n)
      (GlobalTheory.DeRham.spOver Algebra.TensorProduct.includeLeft ≫ tw.y n)
      (GlobalTheory.DeRham.spOver Algebra.TensorProduct.includeRight ≫ tw.y n)
      ((tw.exists_iff n _).1 ⟨_, rfl⟩) ((tw.exists_iff n _).1 ⟨_, rfl⟩)
    refine ⟨u, fun y x => (hu _).trans ?_⟩
    have e : ∀ (ψ : G.A n ⊗[O] G.A n →ₐ[O] O) (i : G.A n →ₐ[O] G.A n ⊗[O] G.A n),
        (Pdiv.ptMap ψ ≫ GlobalTheory.DeRham.spOver i ≫ tw.y n : specO O O ⟶ P.Gt) =
          GlobalTheory.DeRham.spOver (ψ.comp i) ≫ tw.y n := fun ψ i => by
      rw [← GlobalTheory.DeRham.spOver_comp, Category.assoc]
      rfl
    rw [e, e, ev_comp_left, ev_comp_right]
    rfl
  choose u hu using hu
  refine (exists_hom_dual C G u (fun n => ⟨fun x => hi ?_, fun x => hi ?_,
    fun y y' x => hi ?_, fun y y' x => hi ?_⟩) fun n y x => hi ?_).imp
      fun φ hφ s s' n => by rw [hφ]; exact hu n (s.conv n) (s'.conv n)
  · have := weil_pow_left (hp n) (hq n 1) (hq n (.toConv x)) 0
    rw [pow_zero, pow_zero] at this
    rw [hu n 1 (.toConv x), map_one, this, map_one, Units.val_one]
  · have := weil_pow_right (hp n) (hq n 1) (hq n (.toConv x)) 0
    rw [pow_zero, pow_zero] at this
    rw [hu n (.toConv x) 1, map_one, this, map_one, Units.val_one]
  · rw [map_mul, hu n _ (.toConv x), hu n _ (.toConv x), hu n _ (.toConv x), map_mul,
      weil_mul_left (hp n) (hq n _) (hq n _) (hq n _), Units.val_mul]
  · rw [map_mul, hu n (.toConv x), hu n (.toConv x), hu n (.toConv x), map_mul,
      weil_mul_right (hp n) (hq n _) (hq n _) (hq n _), Units.val_mul]
  · have h1 : q (n + 1) (.toConv (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n))) = q n (.toConv x) := by
      refine congrArg P.toA ?_
      change GlobalTheory.DeRham.spOver (x.comp _) ≫ tw.y (n + 1) = GlobalTheory.DeRham.spOver x ≫ tw.y n
      rw [← GlobalTheory.DeRham.spOver_comp, Category.assoc, tw.res]
    have h2 : q n (.toConv (y.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1)))) =
        q (n + 1) (.toConv y) ^ p := by
      refine (congrArg P.toA ?_).trans (map_pow P.toA _ p)
      change GlobalTheory.DeRham.spOver (y.comp _) ≫ tw.y n = (GlobalTheory.DeRham.spOver y ≫ tw.y (n + 1)) ^ p
      rw [← GlobalTheory.DeRham.spOver_comp, Category.assoc, tw.mulP_y, MonObj.comp_pow]
    have a1 := hu (n + 1) (.toConv y) (.toConv (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)))
    have a2 := hu n (.toConv (y.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1)))) (.toConv x)
    rw [h1] at a1
    rw [h2] at a2
    refine a1.trans (Eq.trans ?_ a2.symm)
    exact congrArg Units.val
      (weil_level_left (hp n) (Fact.out : p.Prime).pos (hq n _) (hq (n + 1) _))

end GlobalTheory.WeilPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTransformEqOrientedThetaFunctionCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaOntoF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

theorem algebraMap_half (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)] :
    algebraMap F (AF F) (1 / 2) = ⅟2 := by
  refine (invOf_eq_right_inv ?_).symm
  have h : (2 : AF F) * algebraMap F (AF F) (1 / 2) = algebraMap F (AF F) (2 * (1 / 2)) := by
    rw [map_mul, map_ofNat]
  rw [h]
  norm_num

theorem heisV_comp_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {N : ℕ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N} (ψ : AddChar (AF F) ℂ)
    (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : VA F N) (f : WOF F E nS nT → ℂ) :
    heisV ψ u (f ∘ e.symm) = heisOF σ JS JT ξ₀ ψ (e.symm u) f ∘ e.symm := by
  funext w
  simp only [heisV, heisOF, symplOHF, Function.comp_apply, he, LinearEquiv.apply_symm_apply, map_add,
    algebraMap_half]

theorem exists_thV_eqF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd N e he hrat f hf
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, hcs, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points F E nS nT N e
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR B.ψ hψ N (half F N) half_ne_zero
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, 𝓓, -, hD, h1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  have hsymm : ∀ (u : VA F N) (g : WOF F E nS nT → ℂ),
      heisV B.ψ u (g ∘ e.symm) = heisOF σ JS JT ξ₀ B.ψ (e.symm u) g ∘ e.symm :=
    fun u g => heisV_comp_symm B.ψ he u g
  have hquasi : ∀ g, IsThetaFunOF σ JS JT ξ₀ B.ψ g → QuasiV B.ψ (g ∘ e.symm) := by
    intro g hg a b w
    obtain ⟨x, hx⟩ := GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM F E nS nT N e hrat a b
    have hx' : e.symm (rat a, rat b) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    simp only [Function.comp_apply, map_add, hx', hg.quasi, symplOHF, he, hx, LinearEquiv.apply_symm_apply,
      algebraMap_half]
  have hbdd : ∀ g : VA F N → ℂ, Continuous g → QuasiV B.ψ g → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    intro g hg hq
    obtain ⟨C, hC'⟩ := (hK.prod hK).exists_bound_of_continuousOn hg.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨a, ha⟩ := hKc w.1
    obtain ⟨b, hb⟩ := hKc w.2
    have e1 : w = (rat a, rat b) + (w.1 - rat a, w.2 - rat b) :=
      Prod.ext (by simp) (by simp)
    rw [e1, hq, norm_mul, hψ.2.1, one_mul]
    exact hC' _ ⟨ha, hb⟩
  let 𝒱 : Set (VA F N → ℂ) := {g | ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ g = f ∘ e.symm}
  have hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV B.ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg.cont.comp hcs, hquasi g hg, hbdd _ (hg.cont.comp hcs) (hquasi g hg)⟩
  have hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV B.ψ ν 𝓓 (heisV B.ψ (M t) g) x) (invV B.ψ ν 𝓓 g' x) 0 := by
    rintro _ ⟨g, hg, rfl⟩ M hM
    let L : ℝ →+ WOF F E nS nT := e.symm.toLinearMap.toAddMonoidHom.comp M
    have hL : Continuous L := hcs.comp hM.1
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => (hfin _).2 (by
      have : e (L t) = M t := e.apply_symm_apply _
      rw [this]; exact hM.2 t)
    let g' : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) 0
    have hlev' : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u g' = g' := by
      obtain ⟨U, hUo, hU⟩ := hg.level
      exact ⟨U, hUo, fun u hu h0 =>
        GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g L hL hL0 u h0 (hU u hu h0)⟩
    have hsm' := GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0
    have hg' : IsThetaFunOF σ JS JT ξ₀ B.ψ g' :=
      ⟨GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0, hlev',
        GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g' hlev' hsm', hsm'⟩
    have hds : ∀ w s, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w)
        (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) s := by
      intro w s
      have h1' : HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
          (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) 0 := by
        have e2 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w) = fun t =>
            B.ψ (symplOHF σ JS JT ξ₀ w (L s)) * heisOF σ JS JT ξ₀ B.ψ (L t) g (w + L s) :=
          funext fun t => GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd L hL hL0 g w s t
        rw [e2]
        exact ((GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0 (w + L s)).hasDerivAt).const_mul _
      have h2 := HasDerivAt.comp_sub_const s s (by rwa [sub_self])
        (f := fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
      have e3 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) =
          fun x => heisOF σ JS JT ξ₀ B.ψ (L (s + (x - s))) g w := by
        funext x; rw [add_sub_cancel]
      rw [e3]
      exact h2
    refine ⟨_, ⟨g', hg', rfl⟩, ?_⟩
    obtain ⟨c1, -, C₁, hC₁⟩ := hV _ ⟨g, hg, rfl⟩
    obtain ⟨c2, -, C₂, hC₂⟩ := hV _ ⟨g', hg', rfl⟩
    refine GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam F N B.ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _))
      (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_
    simp only [hsymm, Function.comp_apply]
    exact hds (e.symm w) s
  have hmem : f ∘ e.symm ∈ 𝒱 := ⟨f, hf, rfl⟩
  have hlev : LevelV B.ψ (f ∘ e.symm) := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hcs, fun u hu h0 h0' => ?_⟩
    rw [hsymm, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]
  obtain ⟨hl, hs⟩ := GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev
  have hS : invV B.ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA F (Fin N) :=
    GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz F N _ hl hs (GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates F N B.ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
      (GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay F N B.ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV g hg).2) hder) _ hmem)
  refine ⟨_, hS, ?_⟩
  rw [GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N _ hS)]
  funext w
  simp

end GlobalTheory.ThetaOntoF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentComm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.FiniteInertiaImage

theorem galTate_eq_of_agree {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)) (E : ℕ) (hE0 : 0 < E)
    (hE : ∀ σ ∈ I, galTate A l σ ^ E = 1) {σ τ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ I) (hτ : τ ∈ I)
    (h : ∀ x : ptOver K Ω ⟶ A, x ^ (l ^ 2) = 1 → galPts A σ x = galPts A τ x) :
    galTate A l σ = galTate A l τ := by
  have hu : galTate A l (σ * τ⁻¹) = 1 := by
    refine GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule l (ptOver K Ω ⟶ A) _ E hE0 (hE _ (I.mul_mem hσ (I.inv_mem hτ))) fun t => ?_
    rw [lev_galTate]
    have hy : galPts A τ⁻¹ (t.lev 2) ^ (l ^ 2) = 1 := by rw [← map_pow, t.lev_pow, map_one]
    have e1 : galPts A (σ * τ⁻¹) (t.lev 2) = galPts A σ (galPts A τ⁻¹ (t.lev 2)) := by
      change specAut (σ * τ⁻¹) ≫ t.lev 2 = specAut σ ≫ specAut τ⁻¹ ≫ t.lev 2
      rw [specAut_mul, Category.assoc]
    have e2 : galPts A τ (galPts A τ⁻¹ (t.lev 2)) = t.lev 2 := by
      change specAut τ ≫ specAut τ⁻¹ ≫ t.lev 2 = t.lev 2
      rw [← Category.assoc, ← specAut_mul, mul_inv_cancel, specAut_one, Category.id_comp]
    rw [e1, h _ hy, e2]
  calc galTate A l σ = galTate A l (σ * τ⁻¹ * τ) := by rw [inv_mul_cancel_right]
    _ = galTate A l τ := by rw [map_mul, hu, _root_.one_mul]

theorem finite_image_galTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)),
    Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} →
    (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) →
    (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) →
    (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro K Ω _ _ _ A _ _ l _ I hS _ ⟨E, hE0, hE⟩
  let S := {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1}
  have hmap : ∀ (σ : Ω ≃ₐ[K] Ω) (x : S), galPts A σ x.1 ^ (l ^ 2) = 1 := fun σ x => by
    rw [← map_pow, x.2, map_one]
  let g : (Ω ≃ₐ[K] Ω) → S → S := fun σ x => ⟨galPts A σ x.1, hmap σ x⟩
  let F : galTate A l '' (I : Set (Ω ≃ₐ[K] Ω)) → S → S := fun u => g u.2.choose
  have hF : Function.Injective F := by
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ e
    have h1 := hu.choose_spec
    have h2 := hu'.choose_spec
    refine Subtype.ext ?_
    change u = u'
    rw [← h1.2, ← h2.2]
    refine galTate_eq_of_agree A l I E hE0 hE h1.1 h2.1 fun x hx => ?_
    have := congrFun e ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact Set.finite_coe_iff.1 (Finite.of_injective F hF)

end GlobalTheory.Proof.FiniteInertiaImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEqDimension
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTLat.KernelDim

section

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
  [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem range_alC (h : CokernelBound P) : LinearMap.range P.alC = ⊤ := by
  have hp : ((p : C) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine eq_top_iff.2 fun y hy => ?_
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul c f =>
    obtain ⟨x, hx⟩ := h f
    refine ⟨(c / (p : C) ^ 2) • P.inclT x, ?_⟩
    rw [map_smul, P.alC_inclT, hx, Point.inclOm, TensorProduct.mk_apply, ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def ((p : O) ^ 2), map_pow, map_natCast, smul_eq_mul,
      _root_.mul_one, div_mul_cancel₀ _ hp]

theorem finrank_OmC : Module.finrank C P.OmC = P.A.g := by
  haveI := P.isLocalRing
  haveI := (Point.omega_free_finite_bijective p C v O Λ P).1
  rw [Module.finrank_baseChange, OmegaRank.finrank_omega_Gt p C v O Λ P]

end

theorem finrank_W : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → Module.finrank C P.W = P.A.g := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P h
  have h₁ := LinearMap.finrank_range_add_finrank_ker P.alC
  rw [range_alC P h, finrank_top, finrank_OmC, P.finrank_V] at h₁
  change Module.finrank C (LinearMap.ker P.alC) = _
  omega

end GlobalTheory.HTLat.KernelDim
end

