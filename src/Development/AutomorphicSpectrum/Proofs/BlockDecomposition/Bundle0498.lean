import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WordProd.OneBlockProd

theorem exists_equiv_tensor {α : Type} [Fintype α] [DecidableEq α] (X : α → Type) [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (i₀ : α) (hx : ∀ i, i ≠ i₀ → ∃ v : X i, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w) :
    ∃ (x : ∀ i, X i) (ι : X i₀ ≃ₗ[ℂ] ⨂[ℂ] i, X i),
      ∀ v, ι v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := by
  have hx' : ∀ i, ∃ (x : X i) (c : Module.Dual ℂ (X i)), i ≠ i₀ → c x = 1 ∧ ∀ w, c w • x = w := by
    intro i
    by_cases hi : i = i₀
    · exact ⟨0, 0, fun h => absurd hi h⟩
    · obtain ⟨v, hv, hs⟩ := hx i hi
      obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (X i), f v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
      refine ⟨v, (f v)⁻¹ • f, fun _ => ⟨by simp [hf], fun w => ?_⟩⟩
      obtain ⟨a, rfl⟩ := hs w
      simp [hf, mul_comm]
  choose x c hc using hx'
  let T : X i₀ →ₗ[ℂ] ⨂[ℂ] i, X i := (PiTensorProduct.tprod ℂ).toLinearMap x i₀
  have hT : ∀ v, T v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := fun v => rfl
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    refine (Module.forall_dual_apply_eq_zero_iff ℂ v).1 fun l => ?_
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap
      (Function.update c i₀ l))) hv
    rw [hT, PiTensorProduct.lift.tprod, map_zero] at h1
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
    rw [Finset.prod_eq_single_of_mem i₀ (Finset.mem_univ _) (fun i _ hi => by
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact (hc i hi).1)] at h1
    simpa using h1
  have hsurj : Function.Surjective T := by
    intro y
    refine PiTensorProduct.induction_on y (fun r f => ?_) (fun y z hy hz => ?_)
    · let d : α → ℂ := fun i => if h : i = i₀ then 1 else c i (f i)
      have e1 : f = fun i => d i • Function.update x i₀ (f i₀) i := by
        funext i
        by_cases h : i₀ = i
        · subst h
          simp [d]
        · have h' : i ≠ i₀ := fun e => h e.symm
          simp only [d, dif_neg h', Function.update_of_ne h']
          exact ((hc i h').2 (f i)).symm
      have e2 : PiTensorProduct.tprod ℂ f =
          (∏ i, d i) • PiTensorProduct.tprod ℂ (Function.update x i₀ (f i₀)) := by
        rw [← MultilinearMap.map_smul_univ]
        exact congrArg _ e1
      exact ⟨r • (∏ i, d i) • f i₀, by rw [map_smul, map_smul, hT, e2]⟩
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hz
      exact ⟨u + v, map_add _ _ _⟩
  exact ⟨x, LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible) : ∃ v : V, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w := by
  have hg : ∀ g : G, g = 1 := fun g => Subsingleton.elim _ _
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  refine ⟨v, hv, fun w => ?_⟩
  have : w ∈ S := by rw [hS]; trivial
  exact Submodule.mem_span_singleton.1 this

theorem exists_conj_perm {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (e : n ≃ n) :
    ∃ w : GL n R, ∀ y : GL n R,
      ((w * y * w⁻¹ : GL n R) : Matrix n n R) = (y : Matrix n n R).submatrix e e := by
  let P : Matrix n n R := (1 : Matrix n n R).submatrix e (Equiv.refl n)
  let Q : Matrix n n R := (1 : Matrix n n R).submatrix (Equiv.refl n) e
  have hP : ∀ y : Matrix n n R, P * y = y.submatrix e (Equiv.refl n) := fun y => by
    ext s t
    simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hQ : ∀ y : Matrix n n R, y * Q = y.submatrix (Equiv.refl n) e := fun y => by
    ext s t
    simp [Q, Matrix.mul_apply, Matrix.one_apply]
  have h1 : P * Q = 1 := by
    rw [hQ]
    ext s t
    simp [P, Matrix.one_apply]
  have h2 : Q * P = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨P, Q, h1, h2⟩, fun y => ?_⟩
  show P * (y : Matrix n n R) * Q = _
  rw [hQ, hP]
  rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_parInd {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W}
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hP : ∀ g : GL n k, g ∈ parab k e)
    (hd : ∀ z, deltaHalf k m z = 1) (L : V ≃ₗ[ℂ] W)
    (law0 : ∀ (p : parab k e) v, ρ (leviProj k e p) (L v) = L (π p v)) :
    Nonempty (π.Equiv (parInd e ρ)) := by
  have law : ∀ (p : parab k e) v, twist ρ (deltaHalf k m) (leviProj k e p) (L v) = L (π p v) := fun p v => by
    simp only [twist_apply, hd, Units.val_one, one_smul, law0]
  let f : π.IntertwiningMap (parInd e ρ) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        simp)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩⟩
  · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) h
    simpa using h1
  · have h1 := φ.1.2 ⟨x, hP x⟩ 1
    rw [mul_one] at h1
    refine (law ⟨x, hP x⟩ _).symm.trans ?_
    rw [L.apply_symm_apply]
    exact h1.symm

theorem multiProd_single {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k))
    (g : (Σ i, Fin (b i)) ≃ Fin (b i₀)) :
    Nonempty ((multiProd g fun i => (σ i).ρ).Equiv (σ i₀).ρ) := by
  have hP : ∀ x : GL (Fin (b i₀)) k, x ∈ parab k g := fun x =>
    OneBlockCell.mem_parab_of_single g i₀ h0 x
  have hsub : ∀ i, i ≠ i₀ → Subsingleton (GL (Fin (b i)) k) := by
    intro i hi
    haveI : IsEmpty (Fin (b i)) := by rw [h0 i hi]; infer_instance
    exact ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨x, ι, hι⟩ := exists_equiv_tensor (fun i => (σ i).V) i₀ (fun i hi =>
    haveI := hsub i hi
    exists_line (σ i).ρ (σ i).irr)
  let E : Fin (b i₀) ≃ Fin (b i₀) := (OneBlockCell.valEquiv i₀ rfl h0).symm.trans g
  obtain ⟨w, hw⟩ := exists_conj_perm (R := k) E
  have hwp : ∀ p : parab k g, leviProj k g p i₀ = w * (p : GL (Fin (b i₀)) k) * w⁻¹ := fun p =>
    Units.ext (Matrix.ext fun s t => by
      rw [hw]
      rfl)
  let A : (σ i₀).V ≃ₗ[ℂ] (σ i₀).V := LinearEquiv.ofLinear ((σ i₀).ρ w) ((σ i₀).ρ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  obtain ⟨φ⟩ := nonempty_equiv_parInd (ρ := piTensor fun i => (σ i).ρ) (π := (σ i₀).ρ) g (σ i₀).smooth hP
    (OneBlockCell.deltaHalf_eq_one_of_single i₀ h0) (A.trans ι) (fun p v => by
      show (piTensor fun i => (σ i).ρ) (leviProj k g p) (ι ((σ i₀).ρ w v)) = ι ((σ i₀).ρ w ((σ i₀).ρ p v))
      rw [hι, hι, piTensor_tprod]
      refine congrArg _ (funext fun i => ?_)
      rw [Function.apply_update (fun i u => (σ i).ρ (leviProj k g p i) u)]
      by_cases h : i₀ = i
      · subst h
        rw [Function.update_self, Function.update_self, hwp, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      · have h' : i ≠ i₀ := fun e => h e.symm
        haveI := hsub i h'
        rw [Function.update_of_ne h', Function.update_of_ne h',
          Subsingleton.elim (leviProj k g p i) 1, map_one]
        rfl)
  exact ⟨φ.symm⟩

theorem multiProd_clOf_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL k) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  intro k _ _ _ _ a α _ _ b i₀ hb h0 g
  obtain ⟨N, c⟩ := a
  dsimp only at hb g ⊢
  subst hb
  obtain ⟨φ⟩ := multiProd_single b i₀ h0 (fun i => (clOf ⟨b i₀, c⟩ (b i)).rep) g
  have key : ∀ d : IrrCl (GL (Fin (b i₀)) k), d = c → Nonempty (d.rep.ρ.Equiv c.rep.ρ) := by
    rintro _ rfl
    exact ⟨.refl _⟩
  obtain ⟨ψ⟩ := key _ (clOf_self ⟨b i₀, c⟩)
  exact ⟨φ.trans ψ⟩

end GlobalTheory.CompanionTheory.WordProd.OneBlockProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t), (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main | exact GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphism
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

section twEquiv
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nonempty_twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  have hl : ∀ v, e.toIntertwiningMap.toLinearMap v = e v := fun v => rfl
  have hmap : (GlobalTheory.PRep.twKer ρ N θ).map (e.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.twKer σ N θ := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
      refine ⟨n, e v, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint]
    · rintro ⟨n, w', rfl⟩
      refine ⟨ρ n (e.toLinearEquiv.symm w') - ((θ n : ℂˣ) : ℂ) • e.toLinearEquiv.symm w', ⟨n, _, rfl⟩, ?_⟩
      have hw : e (e.toLinearEquiv.symm w') = w' := e.toLinearEquiv.apply_symm_apply w'
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint, hw]
  refine ⟨Representation.Equiv.mk (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap) fun m => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  exact congrArg (Submodule.Quotient.mk (p := GlobalTheory.PRep.twKer σ N θ)) (eint e (s m) v)

theorem nonempty_twist_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    Nonempty ((twist ρ χ).Equiv (twist σ χ)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  show e.toLinearEquiv (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (e.toLinearEquiv v)
  rw [map_smul, he, he, eint]

end twEquiv

theorem miso_phiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)) (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) := by
  have h1 : MIso (GlobalTheory.BZMir.MRep.phiM k ψ A) (GlobalTheory.BZMir.MRep.phiM k ψ B) := by
    obtain ⟨e⟩ := h
    unfold GlobalTheory.BZMir.MRep.phiM GlobalTheory.BZMir.phiMinus
    generalize_proofs hh
    exact nonempty_twAct_equiv e _ _ _ hh
  obtain ⟨e'⟩ := h1
  exact nonempty_twist_equiv e' _

end GlobalTheory.CompanionTheory.LeibOrd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductRankZeroTrivial
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PhiGpZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mir_zero_eq_one (p : Mir k 0) : p = 1 := by
  have hp := (mem_Mir_iff k (p : GL (Fin 1) k)).1 p.2
  apply Subtype.ext
  apply Units.ext
  ext a b
  obtain rfl : a = Fin.last 0 := Fin.ext (by simp)
  obtain rfl : b = Fin.last 0 := Fin.ext (by simp)
  have := congrFun hp (Fin.last 0)
  simpa [eLast] using this

theorem mirProj_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k n u hu _ _ (Fin.castSucc_ne_last b)]
  simp [one_apply]

theorem conj_mem (n : ℕ) (g u : Mir k n) (hu : u ∈ MirUin k n) : g * u * g⁻¹ ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, mirProj_of_mem n u hu, mul_one, map_inv, mul_inv_cancel]

theorem mem_mirabolicParabolic_zero (m : ℕ) (g : Mir k (m + 1 + 0)) : g ∈ MirabolicParabolic k (m + 1) 0 := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, mem_parab_two]
  intro b
  exact b.elim0

theorem cInd_apply_of_conj {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (u : G)
    (hu : ∀ g : G, ∃ h : g * u * g⁻¹ ∈ H, σ ⟨_, h⟩ = 1) (f : cIndSpace H σ) : cInd H σ u f = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  show f.1.1.1 (g * u) = f.1.1.1 g
  obtain ⟨h, hσ⟩ := hu g
  have hf : f.1.1.1 (g * u * g⁻¹ * g) = σ ⟨_, h⟩ (f.1.1.1 g) := f.1.1.2 ⟨_, h⟩ g
  have e : (g * u * g⁻¹) * g = g * u := by group
  rw [e, hσ] at hf
  exact hf

theorem prodGP_unipotent_apply {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin (m + 1)) k) V) (τ₁ : Representation ℂ (Mir k 0) W)
    (u : Mir k (m + 1 + 0)) (hu : u ∈ MirUin k (m + 1 + 0))
    (f : cIndSpace (MirabolicParabolic k (m + 1) 0) ((extTensor ρ₁ τ₁).comp (gpProj k (m + 1) 0))) :
    prodGP ρ₁ τ₁ u f = f := by
  refine cInd_apply_of_conj _ _ u (fun g => ⟨mem_mirabolicParabolic_zero m _, ?_⟩) f
  have hc := conj_mem (m + 1 + 0) g u hu
  have hp : gpProj k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m (g * u * g⁻¹)⟩ = 1 :=
    Prod.ext (GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m _⟩ hc).1 (mir_zero_eq_one _)
  show (extTensor ρ₁ τ₁) (gpProj k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m (g * u * g⁻¹)⟩) = 1
  rw [hp, map_one]

theorem exists_mirChar_ne (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ) :
    ∃ u : MirUin k (n + 1), mirChar k ψ n u ≠ 1 := by
  obtain ⟨x, hx⟩ := (AddChar.ne_one_iff).1 hψ
  let w : Multiplicative (Fin (n + 1) → k) := Multiplicative.ofAdd (Pi.single (Fin.last n) x)
  let u : MirUin k (n + 1) := ⟨⟨unip k (n + 1) w, MirU_le_Mir k (n + 1) ⟨w, rfl⟩⟩, ⟨w, rfl⟩⟩
  refine ⟨u, ?_⟩
  rw [mirChar_eq k ψ n u w rfl]
  intro h
  apply hx
  have h2 : Circle.toUnits (ψ x) = 1 := by simpa [w] using h
  have h3 : ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) = 1 := by rw [h2]; rfl
  exact Circle.ext (by simpa using h3)

theorem phiN_subsingleton_of_fixed (ψ : AddChar k Circle) {n : ℕ} (X : MRep k (n + 1)) (u : MirUin k (n + 1))
    (hθ : mirChar k ψ n u ≠ 1) (hu : ∀ v, X.ρ (u : Mir k (n + 1)) v = v) : Subsingleton (phiN ψ X).V := by
  have hne : (1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ) ≠ 0 := by
    intro h
    apply hθ
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.1 h).symm
  have top : twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hmem : X.ρ (u : Mir k (n + 1)) v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v ∈
        twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n) := Submodule.subset_span ⟨u, v, rfl⟩
    rw [hu] at hmem
    have e : v = ((1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ))⁻¹ • (v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v) := by
      conv_rhs => rw [show v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v = ((1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ)) • v by
        rw [sub_smul, one_smul]]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  show Subsingleton (X.V ⧸ twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n))
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => exact (Submodule.Quotient.eq _).2 (top ▸ Submodule.mem_top)

theorem phiN_prodGPn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (ρ : GRep k (m + 1)) (τ : MRep k 0)
    (h : (m + 1) + 0 = (m + 0) + 1), IsSmooth ρ.ρ → IsSmooth τ.ρ →
    Subsingleton (phiN ψ (mcast h (prodGPn ρ τ))).V := by
  intro k _ _ _ _ ψ _ hψ m ρ τ h _ _
  obtain ⟨u, hu⟩ := exists_mirChar_ne ψ hψ (m + 0)
  refine phiN_subsingleton_of_fixed ψ (mcast h (prodGPn ρ τ)) u hu ?_
  intro v
  exact prodGP_unipotent_apply _ _ _ u.2 v

end GlobalTheory.CompanionTheory.PhiGpZero

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Cramer

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem mul_adjugate_submatrix (M : Matrix ι (Fin n) K) (f₀ : Fin n → ι) (i : ι) (j : Fin n) :
    (M * adjugate (M.submatrix f₀ id)) i j = mnr M (Function.update f₀ j i) := by
  have h1 : (M * adjugate (M.submatrix f₀ id)) i j = cramer (M.submatrix f₀ id)ᵀ (M i) j := by
    rw [cramer_eq_adjugate_mulVec, ← adjugate_transpose]
    simp [mulVec, dotProduct, mul_apply, transpose_apply, mul_comm]
  rw [h1, cramer_transpose_apply]
  unfold mnr
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab; simp
  · simp [updateRow_apply, hab, Function.update_apply]

theorem eq_mul_of_minor_ratio (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι)
    (h0 : mnr M f₀ ≠ 0) (h0' : mnr M' f₀' ≠ 0)
    (h : ∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') : ∃ c : GL (Fin n) K, M' = M * c.1 := by
  set c := mnr M' f₀' / mnr M f₀ with hcdef
  have hc : ∀ f, mnr M' f = c * mnr M f := fun f => by
    calc mnr M' f = mnr M' f / mnr M' f₀' * mnr M' f₀' := by rw [div_mul_cancel₀ _ h0']
      _ = mnr M f / mnr M f₀ * mnr M' f₀' := by rw [h f]
      _ = c * mnr M f := by rw [hcdef]; ring
  have hc0 : c ≠ 0 := div_ne_zero h0' h0
  set A := M.submatrix f₀ id with hA
  set A' := M'.submatrix f₀ id with hA'
  have hdA : A.det = mnr M f₀ := rfl
  have hdA' : A'.det = c * A.det := hc f₀
  have hA0 : A.det ≠ 0 := h0
  have hdA'0 : A'.det ≠ 0 := by rw [hdA']; exact mul_ne_zero hc0 h0
  have key : M' * adjugate A' = c • (M * adjugate A) := by
    ext i j
    rw [mul_adjugate_submatrix, Matrix.smul_apply, mul_adjugate_submatrix, hc, smul_eq_mul]
  have e1 : M' * adjugate A' * A' = A'.det • M' := by
    rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one]
  have hP : (A⁻¹ * A').det ≠ 0 := by
    rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero h0) hdA'0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (A⁻¹ * A') hP, ?_⟩
  show M' = M * (A⁻¹ * A')
  rw [inv_def, Ring.inverse_eq_inv']
  have e2 : M * ((A.det)⁻¹ • adjugate A * A') = ((A.det)⁻¹ * c⁻¹) • (M' * adjugate A' * A') := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel_right₀ hc0, Matrix.mul_assoc]
  rw [e2, e1, smul_smul, hdA']
  rw [show A.det⁻¹ * c⁻¹ * (c * A.det) = 1 by field_simp, one_smul]

end GlobalTheory.CompanionTheory.GodementH.Cramer

theorem GlobalTheory.CompanionTheory.GodementH.Cramer.main : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  intro K _ ι _ _ n M M' f₀ f₀' h0 h0' h
  exact GlobalTheory.CompanionTheory.GodementH.Cramer.eq_mul_of_minor_ratio M M' f₀ f₀' h0 h0' h
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M) (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i)) (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i)), (∀ i, IsSmooth (ρ' i)) → (∀ i, IsSubquotient (ρ i) (ρ' i)) → IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') := by
  first | exact @GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | exact GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | (intros; apply GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHoldsStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | exact GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | (intros; apply GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsEqEmbeddingStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_eq_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  first | exact @GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts | exact GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts | (intros; apply GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bound_finite_infinite : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ), Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated | exact GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated | (intros; apply GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated <;> assumption)
end

