import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMaximalCompactOpenCompact
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA GlobalTheory.CompanionTheory.ActTr
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FactorAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def fHm (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Hf E a b →* H E a b :=
  (finGL E a).prodMap (finGL E b)

def epsS {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => ((thF E a).comp (locGL E a w.1)).prodMap ((thF E b).comp (locGL E b w.1))

def selS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

theorem continuous_thF (n : ℕ) : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

theorem continuous_loc (n : ℕ) (w : Pl E) : Continuous (locGL E n w) :=
  GlobalTheory.EulerTw.continuous_locGL_spl E n w

theorem continuous_epsS {S : Set (Pl E)} (i : Slot S) : Continuous (epsS a b i) := by
  rcases i with w | w
  · exact (continuous_loc a w.1).prodMap (continuous_loc b w.1)
  · exact ((continuous_thF a).comp (continuous_loc a w.1)).prodMap ((continuous_thF b).comp (continuous_loc b w.1))

theorem embT_prod (w : Pl E) : (embT a w).prodMap (embT b w) =
    (fHm E a b).comp (((thF E a).comp (locGL E a w)).prodMap ((thF E b).comp (locGL E b w))) := by
  refine MonoidHom.ext fun m => Prod.ext ?_ ?_
  · exact GlobalTheory.ThetaPull.thetaA_finGL _
  · exact GlobalTheory.ThetaPull.thetaA_finGL _

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) (G : H E a b → ℂ) :
    actS φ₁ φ₂ i G = act ((fHm E a b).comp (epsS a b i)) (K2 a b i.pl) (selS φ₁ φ₂ i) G := by
  rcases i with w | w
  · rfl
  · show act ((embT a w.1).prodMap (embT b w.1)) (K2 a b w.1) (φ₂ w.1) G = _
    rw [embT_prod]
    rfl

theorem pair_maximal_compact_open_compact (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsOpen (K2 a b w : Set (GLw a w × GLw b w)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1⟩

theorem hecke_of_test {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) (w : Pl E) :
    ∃ A : Subgroup (GLw a w × GLw b w), IsOpen (A : Set (GLw a w × GLw b w)) ∧ IsHecke A (φ w) := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  exact ⟨(K₁ w).prod (K₂ w), (h₁.1 w).1.prod (h₂.1 w).1, h₃.1 w⟩

theorem hecke_sel {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (i : Slot S) :
    ∃ A : Subgroup (GLw a i.pl × GLw b i.pl), IsOpen (A : Set (GLw a i.pl × GLw b i.pl)) ∧ IsHecke A (selS φ₁ φ₂ i) := by
  rcases i with w | w
  · exact hecke_of_test h₁ w.1
  · exact hecke_of_test h₂ w.1

theorem locGL_comm {n : ℕ} {w w' : Pl E} (h : w ≠ w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * locGL E n w' g' = locGL E n w' g' * locGL E n w g := by
  have key : ∀ v, GeneralLinearGroup.map (pLoc E v) (locGL E n w g * locGL E n w' g') =
      GeneralLinearGroup.map (pLoc E v) (locGL E n w' g' * locGL E n w g) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL_of_ne h g', mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv g, mul_one, one_mul]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key v)

theorem thF_loc {n : ℕ} {w u : Pl E} (h : w = GlobalTheory.ThetaSatake.cw u) (g : GLw n w) :
    ∃ g₀ : GLw n u, thF E n (locGL E n w g) = locGL E n u g₀ := by
  subst h
  exact ⟨_, GlobalTheory.ThetaSatake.theta_locGL u g⟩

theorem cw_cw (w : Pl E) : w = GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) :=
  (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm

theorem comm_WT {n : ℕ} {w w' : Pl E} (h : w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * locGL E n w g := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w') g'
  rw [e]
  exact locGL_comm h g g₀

theorem comm_TT {n : ℕ} {w w' : Pl E} (h : GlobalTheory.ThetaSatake.cw w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    thF E n (locGL E n w g) * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * thF E n (locGL E n w g) := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w) g
  obtain ⟨g₁, e'⟩ := thF_loc (cw_cw w') g'
  rw [e, e']
  exact locGL_comm h g₀ g₁

theorem epsS_comm {S : Set (Pl E)} (hS : IsSection S) {i j : Slot S} (hij : i ≠ j)
    (x : GLw a i.pl × GLw b i.pl) (y : GLw a j.pl × GLw b j.pl) :
    epsS a b i x * epsS a b j y = epsS a b j y * epsS a b i x := by
  rcases i with w | w <;> rcases j with w' | w'
  · have hne : w.1 ≠ w'.1 := fun e => hij (congrArg Sum.inl (Subtype.ext e))
    exact Prod.ext (locGL_comm hne _ _) (locGL_comm hne _ _)
  · have hne : w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w'.2.1 w'.2.2 (show GlobalTheory.ThetaSatake.cw w'.1 ∈ S from e ▸ w.2)
    exact Prod.ext (comm_WT hne _ _) (comm_WT hne _ _)
  · have hne : w'.1 ≠ GlobalTheory.ThetaSatake.cw w.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (show GlobalTheory.ThetaSatake.cw w.1 ∈ S from e ▸ w'.2)
    exact Prod.ext (comm_WT hne _ _).symm (comm_WT hne _ _).symm
  · have hne : GlobalTheory.ThetaSatake.cw w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      hij (congrArg Sum.inr (Subtype.ext ((cw_cw w.1).trans ((congrArg GlobalTheory.ThetaSatake.cw e).trans (cw_cw w'.1).symm))))
    exact Prod.ext (comm_TT hne _ _) (comm_TT hne _ _)

theorem selS_conv {S : Set (Pl E)} (φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) :
    selS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i =
      fun m => hint (K2 a b i.pl) fun m' => selS φ₁ φ₂ i m' * selS ψ₁ ψ₂ i (m'⁻¹ * m) := by
  rcases i with w | w <;> rfl

theorem actAlg : ActAlg := by
  intro E _ _ _ a b S hS φ₁ φ₂ ψ₁ ψ₂ hφ₁ hφ₂ hψ₁ hψ₂ G G' hG hG' i j
  have hGl : Lev (fHm E a b) G := hG
  have hGl' : Lev (fHm E a b) G' := hG'
  obtain ⟨hK, hKo⟩ := pair_maximal_compact_open_compact (a := a) (b := b) i.pl
  obtain ⟨hKj, hKoj⟩ := pair_maximal_compact_open_compact (a := a) (b := b) j.pl
  obtain ⟨A, hA, hf⟩ := hecke_sel (S := S) hφ₁ hφ₂ i
  obtain ⟨B, hB, hg⟩ := hecke_sel (S := S) hψ₁ hψ₂ i
  obtain ⟨B', hB', hg'⟩ := hecke_sel (S := S) hψ₁ hψ₂ j
  have ci := continuous_epsS (a := a) (b := b) i
  have cj := continuous_epsS (a := a) (b := b) j
  refine ⟨?_, fun c => ?_, fun hij => ?_, ?_⟩
  · rw [actS_eq]
    exact act_lev ci hK hKo hA hf hGl
  · simp only [actS_eq]
    exact act_add hK hKo hA hf (sm_of_lev ci hGl) (sm_of_lev ci hGl') c
  · simp only [actS_eq]
    refine act_comm hK hKo hA hKj hKoj hB' hf hg' (sm_of_lev ci hGl) (sm_of_lev cj hGl) fun x y => ?_
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, epsS_comm hS hij]
  · simp only [actS_eq]
    rw [selS_conv]
    exact act_conv hK hKo hA hB hf hg (sm_of_lev ci hGl)

end GlobalTheory.CompanionTheory.FactorAction

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairT₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₂_eq {F : H E a b → ℂ} {m : GA E a} {φ : Sm E b} (h : φ.1 = fun x => F (m, x)) : sl₂ F m = φ := by
  have hx : ∃ φ : Sm E b, φ.1 = fun x => F (m, x) := ⟨φ, h⟩
  unfold sl₂
  rw [dif_pos hx]
  exact Subtype.ext (hx.choose_spec.trans h.symm)

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {F G : H E a b → ℂ}

theorem sl₂_val (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) (x : GA E b) :
    (sl₂ F m).1 x = F (m, x) :=
  congrFun ((hS E a b U₁ U₂ F hF).2 m).2 x

theorem sl₂_mem (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) : sl₂ F m ∈ U₂ :=
  ((hS E a b U₁ U₂ F hF).2 m).1

theorem ap₂_add (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₂ T (F + G) = ap₂ T F + ap₂ T G := by
  funext x
  have e : sl₂ (F + G) x.1 = sl₂ F x.1 + sl₂ G x.1 := sl₂_eq (by
    funext y
    exact congrArg₂ (· + ·) (sl₂_val hS hF x.1 y) (sl₂_val hS hG x.1 y))
  change (T (sl₂ (F + G) x.1)).1 x.2 = _
  rw [e, map_add]
  rfl

theorem ap₂_smul (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (c : ℂ) (hF : F ∈ pairSpace U₁ U₂) :
    ap₂ T (c • F) = c • ap₂ T F := by
  funext x
  have e : sl₂ (c • F) x.1 = c • sl₂ F x.1 := sl₂_eq (by
    funext y
    exact congrArg (c * ·) (sl₂_val hS hF x.1 y))
  change (T (sl₂ (c • F) x.1)).1 x.2 = _
  rw [e, map_smul]
  rfl

theorem ap₂_zero (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (U₁ : Submodule ℂ (Sm E a))
    (U₂ : Submodule ℂ (Sm E b)) : ap₂ T (0 : H E a b → ℂ) = 0 := by
  have h := ap₂_smul hS T (0 : ℂ) (Submodule.zero_mem (pairSpace U₁ U₂))
  simpa using h

theorem ap₂_sum (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) {α : Type} (s : Finset α)
    (f : α → H E a b → ℂ) (hf : ∀ j ∈ s, f j ∈ pairSpace U₁ U₂) :
    ap₂ T (∑ j ∈ s, f j) = ∑ j ∈ s, ap₂ T (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₂_zero hS T U₁ U₂
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ap₂_add hS T (hf j (Finset.mem_insert_self j s))
        (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ap₂_rt (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b)
    (x : H E a b) : ap₂ T (fun y => F (y * finH g)) x = ap₂ T F (x * finH g) := by
  have e : sl₂ (fun y => F (y * finH g)) x.1 = act (.fin g.2) (sl₂ F (x.1 * finGL E a g.1)) :=
    sl₂_eq (by
      funext y
      exact (sl₂_val hS hF _ _).trans rfl)
  change (T (sl₂ _ x.1)).1 x.2 = (T (sl₂ F (x.1 * finGL E a g.1))).1 (x.2 * finGL E b g.2)
  rw [e, hT _ _ (sl₂_mem hS hF _)]
  rfl

theorem rt_mem (hU : IsStable U₂) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace (⊤ : Submodule ℂ (Sm E a)) U₂ := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, trivial, act (.fin g.2) φ₂, hU _ _ h₂, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add F G _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem ap₂_mem (hS : PairSlices) {U₂' : Submodule ℂ (Sm E b)} (T : Sm E b →ₗ[ℂ] Sm E b)
    (hTU : ∀ ψ ∈ U₂, T ψ ∈ U₂') (hF : F ∈ pairSpace U₁ U₂) : ap₂ T F ∈ pairSpace U₁ U₂' := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine Submodule.subset_span ⟨φ₁, h₁, T φ₂, hTU _ h₂, ?_⟩
    funext x
    have e : sl₂ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.1 = φ₁.1 x.1 • φ₂ := sl₂_eq rfl
    change (T (sl₂ _ x.1)).1 x.2 = _
    rw [e, map_smul]
    rfl
  | zero =>
    rw [ap₂_zero hS T U₁ U₂]
    exact Submodule.zero_mem _
  | add F G hF hG h₁ h₂ =>
    rw [ap₂_add hS T hF hG]
    exact Submodule.add_mem _ h₁ h₂
  | smul r F hF h =>
    rw [ap₂_smul hS T r hF]
    exact Submodule.smul_mem _ r h

theorem ap₂_type (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (fd₁ : FiniteDimensional ℂ W₁)
    (fd₂ : FiniteDimensional ℂ W₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂)
    (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₂ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · have e : (fun y => F (y * finH ((u₁, u₂) : Hf E a b))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    have h := ap₂_rt hS T hT hF (u₁, u₂) x
    rw [e] at h
    exact h.symm
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ |
        ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :=
      GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ fd₁ fd₂
    let ev : GA E b → Sm E b →ₗ[ℂ] ℂ := fun y =>
      (LinearMap.proj y : (GA E b → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E b).subtype
    have h := GlobalTheory.CompanionTheory.LimV.BlockTy.mem_of_separating
      (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2})
      (fun k : Kinf E a × Kinf E b =>
        act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1)))) ev
      (fun m hm => Subtype.ext (funext hm)) (ev x.2 ∘ₗ T) (fun y => by
        have e : (fun k : Kinf E a × Kinf E b =>
            ev y (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))) =
            fun k => F ((x.1, y) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
          funext fun k => (sl₂_val hS hF _ _).trans rfl
        rw [e]
        exact hty.2 (x.1, y))
    convert h using 2 with k
    have e := hT (.cpt k.2) _ (sl₂_mem hS hF (x.1 * infGL E a (Unitary.toUnits k.1)))
    change _ = (T (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))).1 x.2
    rw [e]
    rfl

theorem ap₂_hecke (hS : PairSlices) {ι : Type} [Fintype ι] (hU : IsStable U₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) {f : ι → H E a b → ℂ}
    (hf : ∀ i, f i ∈ pairSpace U₁ U₂) (h : HeckeM E a b ι) (c : ℂ) (hh : heckeAct h f = c • f) :
    heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i) := by
  funext i x
  have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • fun y => f j (y * finH g) := by
    funext y
    simp [heckeAct, Finsupp.sum, Finset.sum_apply]
  have e₁ : ap₂ T (heckeAct h f i) = c • ap₂ T (f i) := by
    rw [hh]
    exact ap₂_smul hS T c (hf i)
  have e₂ : ap₂ T (heckeAct h f i) x = ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := by
    rw [e, ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun j _ =>
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g),
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ap₂_smul (U₁ := ⊤) (U₂ := U₂) hS T _ (rt_mem hU (hf j) g), Pi.smul_apply, smul_eq_mul,
      ap₂_rt hS T hT (hf j) g x]
  have e₃ : heckeAct h (fun i => ap₂ T (f i)) i x =
      ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := rfl
  rw [e₃, ← e₂, e₁]
  rfl

end GlobalTheory.CompanionTheory.EGlue.PairT₂

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairStep₂ : PairSlices → PairStep₂ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₂ U₂' T f fd₁ fd₂ hU hT hTU hf hty hne
  refine ⟨?_, fun i => PairT₂.ap₂_mem hS T hTU (hf i), fun i => PairT₂.ap₂_type hS fd₁ fd₂ T hT (hf i) (hty i),
    fun h c hh => PairT₂.ap₂_hecke hS hU T hT hf h c hh⟩
  obtain ⟨i, m, φ, hφ, hTφ⟩ := hne
  intro h0
  apply hTφ
  refine Subtype.ext (funext fun y => ?_)
  have e : sl₂ (f i) m = φ := PairT₂.sl₂_eq hφ
  have h1 : ap₂ T (f i) (m, y) = 0 := congrFun (congrFun h0 i) (m, y)
  change (T (sl₂ (f i) m)).1 y = 0 at h1
  rw [e] at h1
  exact h1

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntHaar

open MeasureTheory

variable {k : Type} [Field k]

def glLinearEquiv {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₗ[k] (Fin t → k) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k))
    (Matrix.toLin' ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem coe_glLinearEquiv_symm {t : ℕ} (w : GL (Fin t) k) :
    ((glLinearEquiv w).symm : (Fin t → k) → (Fin t → k)) =
      ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec := by
  funext v
  rfl

theorem det_glLinearEquiv {t : ℕ} (w : GL (Fin t) k) :
    LinearEquiv.det (glLinearEquiv w) = Matrix.GeneralLinearGroup.det w := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k)) = _
  rw [LinearMap.det_toLin']
  rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_inv_mulVec (t : ℕ) [m : MeasurableSpace (Fin t → k)] [hb : BorelSpace (Fin t → k)]
    (μ : Measure (Fin t → k)) [μ.IsAddHaarMeasure] (w : GL (Fin t) k) :
    μ.map ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ := by
  borelize k
  have hp : @BorelSpace (Fin t → k) _ MeasurableSpace.pi := Pi.borelSpace
  have e : m = MeasurableSpace.pi := hb.measurable_eq.trans hp.measurable_eq.symm
  subst e
  rw [← coe_glLinearEquiv_symm, ← det_glLinearEquiv]
  exact GlobalTheory.ChangeVarPi.map_symm_eq_smul k (Fin t) μ (glLinearEquiv w)

theorem smInt_comp_inv_mulVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  intro k _ _ _ _ t _ _ μ _ Z _ _ w φ hl _
  have hc : Continuous ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec :=
    continuous_const.matrix_mulVec continuous_id
  have hval : ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) =
      (((distribHaarChar k (Matrix.GeneralLinearGroup.det w) : NNReal) : ℝ) : ℂ) := by
    rw [detChar_apply, val_absPow, Complex.cpow_one]
    rfl
  rw [hval]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  have hlev : μ ((fun x => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec x)) ⁻¹' {v}) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ (φ ⁻¹' {v}) := by
    rw [← Measure.smul_apply, ← map_inv_mulVec t μ w]
    exact (Measure.map_apply hc.measurable (hl.isOpen_fiber v).measurableSet).symm
  rw [hlev, ENNReal.toReal_smul, smul_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]

end GlobalTheory.CompanionTheory.Rodier.SmIntHaar

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFinite
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem weil_fock_mem (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) (hr : ResEta D χ V.rank) (θ : InfFam D) (hθ : IsInfFam θ)
    (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (hω : IsWeilSch ψ χ θ V μ ω)
    (l : D.what₂.Tau → ℝ) (hl : HasRealPar ψ θ l) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (Φ : schwartzA θ V.rank n) (hΦ : Φ.1 ∈ fockA θ V n l s)
    (k : G D n) (hk : k ∈ K D n) : (ω k Φ).1 ∈ fockA θ V n l s := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

theorem weilKFin : WeilKFin := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  have hfin := GlobalTheory.StdUnn.KFin.fock_kfinite D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  set S := Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ} with hS
  refine ⟨S.map (schwartzA θ V.rank n).subtype, Module.Finite.map S _, ?_, ?_⟩
  · rw [hS, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    exact weil_fock_mem D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ k hk
  · intro k hk
    exact ⟨ω k Φ, Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

