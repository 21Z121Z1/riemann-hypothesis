import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomial
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.ShiftMono

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

theorem mulW_comm (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [G.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  ring

theorem shift_comm (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · show G.mulW 0 u (shift G v x 0) = G.mulW 0 v (shift G u x 0)
    rw [shift_apply_zero, shift_apply_zero, map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext k
  rcases k with _ | k
  · rw [shift_apply_zero, Pi.single_eq_of_ne (by omega)]
  · rw [shift_apply_succ]
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (by omega), map_zero]

variable (s : Fin G.D → Fin G.N → F)

def mono (α : Fin G.D →₀ ℕ) {j l : ℕ} (h : j + α.degree = l) : G.Sec j →ₗ[F] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) (⟨α, rfl⟩ : MonoDeg (Fin G.D) α.degree)
    ((Nat.cast_add j _).symm.trans (congrArg _ h))

theorem mono_add (α β γ : Fin G.D →₀ ℕ) (e : γ = α + β) {j l' l : ℕ} (h : j + γ.degree = l)
    (h₂ : j + β.degree = l') (h₁ : l' + α.degree = l) (m : G.Sec j) :
    mono G s γ h m = mono G s α h₁ (mono G s β h₂ m) := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_add]
  ring

theorem mono_zero (α : Fin G.D →₀ ℕ) (e : α = 0) {j : ℕ} (h : j + α.degree = j) (m : G.Sec j) :
    mono G s α h m = m := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_zero, one_mul]

theorem mono_single (i : Fin G.D) {j : ℕ} (h : j + (Finsupp.single i 1).degree = j + 1) (m : G.Sec j) :
    mono G s (Finsupp.single i 1) h m = G.mulW j (s i) m := by
  rw [G.mulW_apply]
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_single, pow_one]

def Acts (E : Module.End F (Tot G)) (α : Fin G.D →₀ ℕ) : Prop :=
  ∀ (j l : ℕ) (h : j + α.degree = l) (m : G.Sec j), E (Pi.single j m) = Pi.single l (mono G s α h m)

theorem acts_one : Acts G s 1 0 := fun j l h m => by
  obtain rfl : j = l := by simpa using h
  rw [mono_zero G s 0 rfl h m]; rfl

theorem acts_mul {E₁ E₂ : Module.End F (Tot G)} {α₁ α₂ : Fin G.D →₀ ℕ} (h₁ : Acts G s E₁ α₁) (h₂ : Acts G s E₂ α₂) :
    Acts G s (E₁ * E₂) (α₁ + α₂) := fun j l h m => by
  have h' : j + α₂.degree + α₁.degree = l := by rw [map_add] at h; omega
  rw [Module.End.mul_apply, h₂ j (j + α₂.degree) rfl m, h₁ (j + α₂.degree) l h',
    ← mono_add G s α₁ α₂ (α₁ + α₂) rfl]

theorem acts_shift (i : Fin G.D) : Acts G s (shift G (s i)) (Finsupp.single i 1) := fun j l h m => by
  obtain rfl : l = j + 1 := by simpa using h.symm
  rw [shift_single, mono_single]

theorem acts_pow (i : Fin G.D) (k : ℕ) : Acts G s (shift G (s i) ^ k) (Finsupp.single i k) := by
  induction k with
  | zero => simpa using acts_one G s
  | succ k ih =>
    rw [pow_succ, show Finsupp.single i (k + 1) = Finsupp.single i k + Finsupp.single i 1 by simp]
    exact acts_mul G s ih (acts_shift G s i)

theorem acts_list : ∀ (n : ℕ) (E : Fin n → Module.End F (Tot G)) (g : Fin n → Fin G.D →₀ ℕ),
    (∀ i, Acts G s (E i) (g i)) → Acts G s (List.ofFn E).prod (∑ i, g i)
  | 0, E, g, _ => by simpa using acts_one G s
  | n + 1, E, g, hE => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact acts_mul G s (hE 0) (acts_list n _ _ fun i => hE i.succ)

theorem acts_pw (α : Fin G.D →₀ ℕ) : Acts G s (HSShort.pw (shift G) s α) α := by
  have := acts_list G s G.D (fun i => shift G (s i) ^ α i) (fun i => Finsupp.single i (α i))
    fun i => acts_pow G s i (α i)
  rwa [Finsupp.univ_sum_single] at this

end GlobalTheory.HSShort.ShiftMono

namespace GlobalTheory.HSShort

theorem shift_comm_single_mono : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F),
    (∀ u v, shift G u * shift G v = shift G v * shift G u) ∧ (∀ (j : ℕ) u (m : G.Sec j), shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m)) ∧ ∀ (s : Fin G.D → Fin G.N → F) (a j l : ℕ) (h : j + a = l) (α : MonoDeg (Fin G.D) a) (m : G.Sec j), pw (shift G) s α.1 (Pi.single j m) = Pi.single l (mulPow G s h α m) := by
  intro F _ _ G
  refine ⟨ShiftMono.shift_comm G, ShiftMono.shift_single G, fun s a j l h α m => ?_⟩
  obtain ⟨α, rfl⟩ := α
  exact ShiftMono.acts_pw G s α j l h m

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialStabilizerTransferConjSelfDualLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TransferHyp

theorem stab_iff_entries {R : Type} [CommRing R] {n : ℕ} (O : Subring R) {X Y : Matrix (Fin n) (Fin n) R}
    (hXY : X * Y = 1) (hYX : Y * X = 1) :
    (∀ z : Fin n → R, (∀ i, z i ∈ O) ↔ ∀ i, X.mulVec z i ∈ O) ↔ (∀ i j, X i j ∈ O) ∧ ∀ i j, Y i j ∈ O := by
  have hs : ∀ j i : Fin n, (Pi.single j 1 : Fin n → R) i ∈ O := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hm : ∀ {A : Matrix (Fin n) (Fin n) R}, (∀ i j, A i j ∈ O) → ∀ z : Fin n → R, (∀ i, z i ∈ O) →
      ∀ i, A.mulVec z i ∈ O := fun {A} hA z hz i => by
    change ∑ j, A i j * z j ∈ O
    exact sum_mem fun j _ => mul_mem (hA i j) (hz j)
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using (h _).1 (hs j) i
    · have := (h (Y.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]
        exact hs j) i
      simpa using this
  · rintro ⟨h1, h2⟩ z
    refine ⟨hm h1 z, fun hz => ?_⟩
    have := hm h2 _ hz
    rwa [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] at this

theorem stab_conj {R : Type} [CommRing R] {n : ℕ} (I Λ : (Fin n → R) → Prop) {A B H G X : Matrix (Fin n) (Fin n) R}
    (hAB : A * B = 1) (hBA : B * A = 1) (hHG : H * G = 1)
    (hΛ : ∀ y, Λ y ↔ I (B.mulVec (H.mulVec y))) :
    (∀ y, Λ y ↔ Λ ((G * (A * X * B) * H).mulVec y)) ↔ ∀ z, I z ↔ I (X.mulVec z) := by
  have key : ∀ y, B.mulVec (H.mulVec ((G * (A * X * B) * H).mulVec y)) = X.mulVec (B.mulVec (H.mulVec y)) := fun y => by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    calc B * (H * (G * (A * X * B) * H)) = B * (H * G) * A * X * (B * H) := by simp only [Matrix.mul_assoc]
      _ = X * (B * H) := by rw [hHG, Matrix.mul_one, hBA, Matrix.one_mul]
  simp only [hΛ, key]
  refine ⟨fun h z => ?_, fun h y => h _⟩
  have e : B.mulVec (H.mulVec (G.mulVec (A.mulVec z))) = z := by
    rw [Matrix.mulVec_mulVec _ H, hHG, Matrix.one_mulVec, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  have := h (G.mulVec (A.mulVec z))
  rwa [e] at this

theorem finMat_mul {D : D7} (V : HSp D) (g h : GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h :=
  congrArg Units.val (map_mul (finHom V) g h)

theorem finMat_one {D : D7} (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 :=
  congrArg Units.val (map_one (finHom V))

def finComp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Ad E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
  (GlobalTheory.LFun.finAdEquiv F E).symm.toRingHom.comp (pFin E)

def intRing (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
  ⨅ u : HeightOneSpectrum (𝓞 E), (Ov E u).comap (GlobalTheory.LFun.compAt F u)

theorem mem_intRing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) : z ∈ intRing F E ↔ ∀ u, GlobalTheory.LFun.compAt F u z ∈ Ov E u := by
  simp only [intRing, Subring.mem_iInf, Subring.mem_comap]

theorem stab_finComp_iff (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMField E] {n : ℕ} (x : UA E n) :
    (∀ z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E, (∀ i, z i ∈ intRing F E) ↔
      ∀ i, (x.1.1.map (finComp F E)).mulVec z i ∈ intRing F E) ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  have hκ : ∀ (y : UA E n) a b, (y.1.1.map (finComp F E)) a b ∈ intRing F E ↔
      ∀ u, (cLoc u y).1 a b ∈ u.adicCompletionIntegers E := fun y a b => by
    refine (mem_intRing _).trans (forall_congr' fun u => ?_)
    have e : GlobalTheory.LFun.compAt F u ((y.1.1.map (finComp F E)) a b) = (cLoc u y).1 a b :=
      congrArg (fun t => pLoc E u t) ((GlobalTheory.LFun.finAdEquiv F E).apply_symm_apply (pFin E (y.1.1 a b)))
    rw [e]
    exact Iff.rfl
  have hXY : ∀ y : UA E n, y.1.1.map (finComp F E) * (y⁻¹).1.1.map (finComp F E) = 1 := fun y => by
    rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX := hXY x⁻¹
  rw [inv_inv] at hYX
  refine (stab_iff_entries _ (hXY x) hYX).trans ?_
  simp only [hκ]

theorem mem_KGL_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {x : UA E n} (hx : x ∈ locU n P) : cLoc P x ∈ GlobalTheory.LFun.KGL P n ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  constructor
  · intro h2
    exact ⟨fun a b u => GlobalTheory.UnramDict.cLoc_entry_mem hx h2 u a b, fun a b u =>
      GlobalTheory.UnramDict.cLoc_entry_mem (inv_mem hx) (by rw [map_inv]; exact inv_mem h2) u a b⟩
  · rintro ⟨h4, h5⟩
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun a b => h4 a b P, fun a b => ?_⟩
    rw [← map_inv]
    exact h5 a b P

theorem map_mul_map_inv {K R : Type} [Field K] [CommRing R] {n : ℕ} (ι : K →+* R) {M N : Matrix (Fin n) (Fin n) K}
    (h : N * M = 1) : M.map ι * M⁻¹.map ι = 1 ∧ M⁻¹.map ι * M.map ι = 1 := by
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse h
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]

theorem cj_mem_hyp_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P := by
  intro D _ V j h₀ M hM _ _ hj hlat hloc P x
  have hO : ∀ z, z ∈ intAE D ↔ z ∈ intRing D.host.F D.host.E := fun z =>
    (GlobalTheory.LFun.mem_intAE_iff_compAt z).trans (mem_intRing z).symm
  obtain ⟨hAB, hBA⟩ := map_mul_map_inv (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E).toRingHom hM
  have hHG : finMat D.sp.cm.sig V.gram h₀ * finMat D.sp.cm.sig V.gram h₀⁻¹ = 1 := by
    rw [← finMat_mul, mul_inv_cancel, finMat_one]
  have hst : (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram (cj j h₀ x)).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ↔
      (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers D.host.E) ∧
        ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers D.host.E := by
    rw [cj_apply, finMat_mul, finMat_mul, hj]
    exact (stab_conj (fun z => ∀ i, z i ∈ intRing D.host.F D.host.E)
      (fun y => y ∈ latHat D.host.F D.host.E (L0c D V)) hAB hBA hHG
      fun y => (hlat y).trans (forall_congr' fun i => hO _)).trans (stab_finComp_iff D.host.F x)
  constructor
  · rintro ⟨⟨h1, h2, -⟩, e, f, hef, h3⟩
    have hx := (hloc P e f hef x).2 ⟨h1, h3⟩
    exact ⟨hx, (mem_KGL_iff hx).2 (hst.1 h2)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e, f, hef⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.LFun.comp_finAdEquiv D) P
    obtain ⟨h3, h4⟩ := (hloc P e f hef x).1 h1
    exact ⟨⟨h3, hst.2 ((mem_KGL_iff h1).1 h2), fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, hef, h4⟩

end GlobalTheory.TransferHyp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Y0_mul_apply {a n : ℕ} (M : Matrix (Fin (a + n)) (Fin (a + n)) k) (i : Fin n) (j : Fin (a + n)) :
    (Y0 k n (a + n) * M) i j = M (Fin.natAdd a i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]
  · simp [Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = a + i) := fun h => hl (Fin.ext (by simp; omega))
    simp [Y0, this]
  · simp

theorem mul_Y0_apply {a n : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin (a + n)) :
    (D * Y0 k n (a + n)) i j = if h : a ≤ (j : ℕ) then D i ⟨j - a, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]
    · simp [Y0]; omega
    · intro l _ hl
      have : ¬ ((j : ℕ) = a + l) := fun h' => hl (Fin.ext (by simp; omega))
      simp [Y0, this]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) = a + l) := by omega
    simp [Y0, this]

theorem Y0_mul_parab {a n : ℕ} (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    Y0 k n (a + n) * (p : GL (Fin (a + n)) k).1 =
      (leviProj k (GlobalTheory.RankFibre.blocks a n) p true : GL (Fin n) k).1 * Y0 k n (a + n) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have hp := (mem_parab_two k).1 p.2
  split_ifs with h
  · rw [leviProj_apply]
    have e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i := Fin.ext (by simp [stdSum])
    have e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j := Fin.ext (by simp [stdSum]; omega)
    rw [e1, e2]
  · have := hp i ⟨j, by omega⟩
    simpa [stdSum] using this

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parChar_eq {a n : ℕ} (ν : kˣ →* ℂˣ) (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    ((GlobalTheory.RankFibre.parChar ν ν⁻¹ a n p : ℂˣ) : ℂ) =
      apow (gdet (p : GL (Fin (a + n)) k)) ((n : ℂ) / 2) *
        ((((ν (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)) (-((a + n : ℕ) : ℂ) / 2)) := by
  set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false
  set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true
  have hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) =
      absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D) := by
    rw [← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]
    simp [A, D]
    rfl
  have hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D := by
    rw [gdet, det_parab, Fintype.prod_bool, mul_comm]
  simp only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]
  rw [hdet, apow_mul]
  have e : apow (gdet D) (-(a : ℂ) / 2) =
      apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2) := by
    rw [← apow_add]; congr 1; push_cast; ring
  show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) *
    ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _
  rw [e, mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]
  ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detTw (d : ℕ) (s : ℂ) : (GL (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ) where
  toFun f x := apow (gdet x) s * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

theorem detTw_apply (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (x : GL (Fin d) k) :
    detTw d s f x = apow (gdet x) s * f x := rfl

theorem detTw_neg_detTw (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d (-s) (detTw d s f) = f := by
  funext x; rw [detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]; simp

theorem detTw_detTw_neg (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d s (detTw d (-s) f) = f := by
  simpa using detTw_neg_detTw d (-s) f

theorem detTw_translate (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (h : GL (Fin d) k) :
    (fun x => detTw d s f (x * h)) = apow (gdet h) s • detTw d s (fun x => f (x * h)) := by
  funext x
  simp only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]
  ring

theorem detTw_mem_indScal {a n : ℕ} (ν : kˣ →* ℂˣ) {f : GL (Fin (a + n)) k → ℂ} (hf : f ∈ indSp k n (a + n) ν) :
    detTw (a + n) ((n : ℂ) / 2) f ∈ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := by
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩
  · have hg2 : apow (gdet g) ((n : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]
  · intro p x
    have h := hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)
    simp only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]
    ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv

open IndTwist

theorem indSp_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro P k _ _ _ _ n d ν hn hνs hνu N hN hinv
  obtain ⟨a, rfl⟩ : ∃ a, d = a + n := ⟨d - n, by omega⟩
  have hu : IsUnitaryChar ν⁻¹ := fun g => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]
  set s : ℂ := (n : ℂ) / 2
  let M : Submodule ℂ (GL (Fin (a + n)) k → ℂ) := N.comap (detTw (a + n) (-s))
  have hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := fun g hg => by
    have := detTw_mem_indScal ν (hN hg)
    rwa [detTw_detTw_neg] at this
  have hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M := fun g hg h => by
    show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N
    have e : detTw (a + n) (-s) (fun x => g (x * h)) =
        apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h)) := by
      rw [detTw_translate, smul_smul, ← apow_add]; simp
    rw [e]
    exact N.smul_mem _ (hinv _ hg h)
  have hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M := fun f hf => by
    show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N
    rwa [detTw_neg_detTw]
  rcases GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu
    M hMle hMinv with h | h
  · left
    refine (Submodule.eq_bot_iff N).2 fun f hf => ?_
    have h0 : detTw (a + n) s f = 0 := by
      have := hmemM f hf
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    rw [← detTw_neg_detTw (a + n) s f, h0, map_zero]
  · right
    refine le_antisymm hN fun f hf => ?_
    have := h (detTw_mem_indScal ν hf)
    have h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N := this
    rwa [detTw_neg_detTw] at h'

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertTensorField

theorem isField_tensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp

end GlobalTheory.InertTensorField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceEndomorphismStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_congruence_endomorphism : ∀ (D : D7) (V : HSp D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ (N : ℕ), 0 < N → ∀ κ : GA D V, FinCong V 1 κ → ∃ γ₀ : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (γ₀ a)) = N • w := by
  first | exact @GlobalTheory.GeoLevel.exists_endo_approx | exact GlobalTheory.GeoLevel.exists_endo_approx | (intros; apply GlobalTheory.GeoLevel.exists_endo_approx <;> assumption)
end

