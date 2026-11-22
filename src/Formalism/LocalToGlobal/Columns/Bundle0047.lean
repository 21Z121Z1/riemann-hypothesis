import Formalism.LocalToGlobal.Columns.Bundle0043
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral
import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedBack
import Formalism.LocalToGlobal.Columns.ColumnDeterminants.ColsTiedD
import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.GlobalTheory.WindowConstantGeSixteen

-- bundled from Formalism.LocalToGlobal.Columns.LevelZeroComparisonBijective
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}

attribute [local instance] ptYAct

variable (Λ L) in

structure Step0Hyp : Prop where
  uniq : ∀ b b' : L.β 0, b = b'
  levG : ∀ b, L.levG 0 b = Λ 0
  levQ : ∀ b, L.levQ 0 b = LevQFam.top X.E X.K (R.N 0) (QE sel (mu : Chr X.F X.E X.K))

theorem mem_grp_of_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))} {Λ₁ Λ₂ : LevFam E K n SG}
    (h : Λ₁ = Λ₂) {g : GLG E n SG} (hg : g ∈ Λ₁.grp) : g ∈ Λ₂.grp := h ▸ hg

theorem frame_move {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)}
    {f f' γ : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E n P)
    (hN : localization₂ P.asIdeal N = localization₂ P.asIdeal (gmap γ N')) : f⁻¹ * γ * f' ∈ GLint E n P := by
  intro x
  show f.symm (γ (f' x)) ∈ stdAt E n P ↔ x ∈ stdAt E n P
  rw [← hf, LinearEquiv.apply_symm_apply, hN, mem_localization_gmap, LinearEquiv.symm_apply_apply, hf']

def levelZeroClassMap (c : (chFY W sel mu cst L u m2 0).Cl) : StCl W Λ u 0 := (stepGSD W Λ u 0).cls (classRepresentativePair c).deco

def stabZeroY (H : Step0Hyp Λ L) {b : L.β 0} (x : PtY W cst L u m2 0 b) :
    MulAction.stabilizer ((chFY W sel mu cst L u m2 0).mem b).G x → MulAction.stabilizer (stepGSD W Λ u 0).G x.deco :=
  fun g => ⟨(g.1.1, ⟨g.1.2.1.1, mem_grp_of_eq (H.levG b) g.1.2.1.2⟩), congrArg PtY.deco g.2⟩

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))

variable (W Λ cst L u m2) in

def e0LY : (StCl W Λ u 0 → FrS X σ₀ (R.N 0) → ℂ) →ₗ[ℂ] ((chFY W sel mu cst L u m2 0).Cl → FrS X σ₀ (R.N 0) → ℂ) where
  toFun F c := (stepEv W Λ σ₀ hσ u 0).atPt (classRepresentativePair c).deco F
  map_add' F G := by
    funext c
    exact map_add ((stepEv W Λ σ₀ hσ u 0).trPt (classRepresentativePair c).deco) _ _
  map_smul' t F := by
    funext c
    exact map_smul ((stepEv W Λ σ₀ hσ u 0).trPt (classRepresentativePair c).deco) t _

end Zero

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OcbTIntOfStab
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Tr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ocbT_bEnt_comp (hq0 : (q : E) ≠ 0) {n' c' n c : ℕ} (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c))
    {l s : ℕ} (hl : l < n + c) (hs : s < n' + c') :
    ocbBEnt n' n q (g ∘ₗ y) l s = ∑ m : Fin (n + c), ocbBEnt n n q g l m.1 * ocbBEnt n' n q y m.1 s := by
  unfold ocbBEnt
  rw [ocbS_atN_comp g y hl hs, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hz : ((q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)) =
      (q : E) ^ (LocE.scE n (fun i => i + 1) m.1 - LocE.scE n (fun i => i + 1) l) *
        (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) m.1) := by
    rw [← zpow_add₀ hq0]
    congr 1
    ring
  rw [hz]
  ring

private theorem intAt_apply_of_mem_stdAt {N : ℕ} {x : Sp E N} (hx : x ∈ stdAt E N P) (i : Fin N) : IntAt P (x i) := by
  obtain ⟨s, hs, hsx⟩ := hx
  rw [mem_stdLat] at hsx
  obtain ⟨r, hr⟩ := hsx i
  exact ⟨r, s, hs, by rw [hr]; simp [Algebra.smul_def]⟩

private theorem mem_sclLat_iff_scaled_mem_stdAt {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ LocE.sclLat P q N e ↔ (fun l : Fin N => ((q : E) ^ e l)⁻¹ * x l) ∈ stdAt E N P := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap]
  rfl

theorem ocbT_int_of_stab (hq0 : (q : E) ≠ 0) {n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) {l m : ℕ} (hl : l < n + c) (hm : m < n + c) :
    IntAt P (ocbBEnt n n q g.toLinearMap l m) := by
  set e := LocE.scE n (fun i => i + 1) with he
  let v : Sp E (n + c) := fun i => if (i : ℕ) = m then (q : E) ^ (e m) else 0
  have hv : v ∈ LocE.lamY P q n c (fun i => i + 1) := by
    unfold LocE.lamY
    rw [mem_sclLat_iff_scaled_mem_stdAt]
    refine ⟨1, one_mem _, ?_⟩
    rw [one_smul, mem_stdLat]
    intro i
    by_cases hi : (i : ℕ) = m
    · refine ⟨1, ?_⟩
      simp only [v, hi, if_true, map_one]
      rw [← he, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
    · exact ⟨0, by simp [v, hi]⟩
  have hg' : ∀ x, g x ∈ LocE.lamY P q n c (fun i => i + 1) ↔ x ∈ LocE.lamY P q n c (fun i => i + 1) := hg
  have hgv := (hg' v).2 hv
  unfold LocE.lamY at hgv
  rw [mem_sclLat_iff_scaled_mem_stdAt] at hgv
  have hint := intAt_apply_of_mem_stdAt hgv ⟨l, hl⟩
  have hv' : v = ((q : E) ^ (e m)) • Loc.eN E (n + c) m := by
    funext i
    by_cases hi : (i : ℕ) = m <;> simp [v, Loc.eN, hi]
  convert hint using 1
  unfold ocbBEnt
  rw [ocbS_atN_of_lt _ hl]
  simp only [LinearEquiv.coe_coe, hv', map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← he, zpow_sub₀ hq0]
  ring

theorem ocbT_bEnt_id {n c l s : ℕ} (hl : l < n + c) :
    ocbBEnt n n q (LinearMap.id : Sp E (n + c) →ₗ[E] Sp E (n + c)) l s = if l = s then 1 else 0 := by
  unfold ocbBEnt
  rw [LinearMap.id_apply, ocbS_atN_of_lt _ hl]
  by_cases h : l = s
  · subst h
    simp [Loc.eN]
  · simp [Loc.eN, h]

theorem ocbT_red_symm (hq0 : (q : E) ≠ 0) {n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) {l s : ℕ} (hl : l < n + c) (hs : s < n + c) :
    Loc.atN (hbar.symm (Loc.eN _ (n + c) s)) l = redP P (ocbBEnt n n q h₀.symm.toLinearMap l s) := by
  classical
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hI1 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hh₀ hi hm
  have hI2 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.symm.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hsymm hi hm
  have hDA : LinearMap.toMatrix' hbar.symm.toLinearMap * LinearMap.toMatrix' hbar.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hAC : LinearMap.toMatrix' hbar.toLinearMap *
      (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hcomp := ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap i.2 j.2
    rw [LinearEquiv.comp_symm, ocbT_bEnt_id i.2] at hcomp
    have hsum : ∑ m : Fin (n + c), LinearMap.toMatrix' hbar.toLinearMap i m *
        (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) m j =
        redP P (∑ m : Fin (n + c),
          ocbBEnt n n q h₀.toLinearMap i m * ocbBEnt n n q h₀.symm.toLinearMap m j) := by
      rw [redP_sum _ _ (fun m _ => IntAt.mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2))]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [reduction_mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2), Matrix.of_apply, ocbS_atN_toMatrix']
      congr 1
      exact (hred₀ _ _ i.2 m.2).2
    rw [hsum, ← hcomp, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [redP_one]
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hij', redP_zero]
  have hCD : (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) =
      LinearMap.toMatrix' hbar.symm.toLinearMap := by
    rw [← Matrix.one_mul (Matrix.of _), ← hDA, Matrix.mul_assoc, hAC, Matrix.mul_one]
  have h1 := congrFun (congrFun hCD ⟨l, hl⟩) ⟨s, hs⟩
  rw [Matrix.of_apply, ocbS_atN_toMatrix'] at h1
  exact h1.symm

theorem ocbT_trans (hq0 : (q : E) ≠ 0) {K L : Type} [Field K] [Field L] (σ : K →+* L) {n' c' c'' n c : ℕ} (hcc : c' = c'')
    {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) (Φ : Loc.SF E K (n' + c') (n + c)) (Φr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + c'') (n + c))
    (hsupp : ∀ y, Φ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Φ y) = Φr ybar) :
    (∀ y, Φ (h₀.symm.toLinearMap ∘ₗ y) ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) ∧
    (∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) →
        σ (Φ (h₀.symm.toLinearMap ∘ₗ y)) = Φr (hbar.symm.toLinearMap ∘ₗ ybar)) := by
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hcomp_int : ∀ (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)),
      (∀ l m, l < n + c → m < n + c → IntAt P (ocbBEnt n n q g l m)) →
      (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q (g ∘ₗ y) l s) := by
    intro g y hg hy l s hl hs
    rw [ocbT_bEnt_comp hq0 g y hl hs]
    exact ciIntAt_sum _ _ (fun m _ => IntAt.mul (hg _ _ hl m.2) (hy _ _ m.2 hs))
  refine ⟨fun y hy => ?_, fun y ybar hy hyb => ?_⟩
  · have h1 := hsupp _ hy
    have h2 := hcomp_int h₀.toLinearMap _ (fun l m hl hm => ocbT_int_of_stab hq0 hh₀ hl hm) h1
    have he : h₀.toLinearMap ∘ₗ (h₀.symm.toLinearMap ∘ₗ y) = y := by
      rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]
    rwa [he] at h2
  · have hI := hcomp_int h₀.symm.toLinearMap y (fun l m hl hm => ocbT_int_of_stab hq0 hsymm hl hm) hy
    apply hred _ _ hI
    intro l s hl hs
    have hs' : s < n' + c'' := by omega
    rw [ocbS_atN_comp _ _ hl hs', ocbT_bEnt_comp hq0 _ _ hl hs,
      redP_sum _ _ (fun m _ => IntAt.mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [reduction_mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs), hyb _ _ m.2 hs]
    congr 1
    exact ocbT_red_symm hq0 hh₀ hred₀ hl m.2

end Tr

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecPerFF
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

def zOfRow0 (σ₀ : X.K →+* ℂ) (hM : (rowGSD W ΛM).Ok) (F : (rowGSD W ΛM).EqFun) : Fin ((rowGSD W ΛM).hDim hM) → ℂ :=
  fun a => σ₀ (((rowGSD W ΛM).hB hM).repr F a)

end Gen

section Cast

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem levFam_eq_cast {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG')
    (A : LevFam E K n SG) (B : LevFam E K n SG') (h : ∀ (w : SG') (hw : w.1 ∈ SG), B w = A ⟨w.1, hw⟩) : B = e ▸ A := by
  subst e
  funext w
  exact h w w.2

def decoCast {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG') (d : DecoSet E n ∅ SG) :
    DecoSet E n ∅ SG' := e ▸ d

variable {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
  (Λ' : LevFam X.E X.K (R.N R.m - 1) SG')

def rowCast (hΛ : Λ' = e ▸ A) (F : (formGSD (rowVal W SG') Λ').EqFun) : (rowGSD W A).EqFun := by
  subst hΛ
  subst e
  exact F

end Cast

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs)

theorem rowTy_inv_cast : (rowTy Ch sel mu P).inv = rcol_rowSG_eq sel mu hQ ▸ (rowTyG Ch P).inv := by
  refine levFam_eq_cast (rcol_rowSG_eq sel mu hQ) _ _ fun w hw => ?_
  first
  | (simp only [LevFam.inv, rowTy, LevFam.glue, dif_pos hw]; done)
  | (unfold LevFam.inv rowTy LevFam.glue; rw [dif_pos hw])
  | (simp [LevFam.inv, rowTy, LevFam.glue, hw])

def zOfRow (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) (F : MtildeV W Ch sel mu P) : Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ :=
  zOfRow0 W (rowTyG Ch P).inv σ₀ hM (rowCast W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P) F)

end Main

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.Target
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

structure ColJoint (c : ColRec) (C : ColObj c.what₂.LL c.what₂.Word) where
  isoF : ∀ u, Formalism.L2.GlobalTheoryTheory.HLatOps.Iso ((c.fm u).lat 0) (C.Mf u)
  ram : ∀ u, ((c.fm u).ramSub).map (isoF u).e.toLinearMap = LinearMap.range (C.incl u)
  T_eq : ∀ u, (c.mem u).A.T = C.T u
  f_eq : C.f = c.R.f
  k_eq : C.k = c.R.k
  m_eq : C.m = c.R.m
  Dstar_eq : ∀ u, (c.mem u).A.Dstar = C.Dstar

  duStar_eq : ∀ u, ((c.mem u).A.duStar : ℝ) = C.dstar u

def ColObj.onRec (D : D7) {c : ColRec} (h : D.colRec = c) (C : ColObj c.what₂.LL c.what₂.Word) : ColObj D.what₂.LL D.what₂.Word := by
  subst h
  exact C

def ColJoint.onRec (D : D7) {c : ColRec} (h : D.colRec = c) {C : ColObj c.what₂.LL c.what₂.Word} (J : ColJoint c C) :
    ColJoint D.colRec (ColObj.onRec D h C) := by
  subst h
  exact J

structure ColObj.InclOk {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I) : Prop where
  inj : ∀ u, Function.Injective (C.incl u)
  norm : ∀ u v (x : (C.M u).V),
    Formalism.HermitianLatticesTheory.normAt (C.M u).b (C.M u).X v x = Formalism.HermitianLatticesTheory.normAt (C.Mf u).b (C.Mf u).X v (C.incl u x)
  L : ∀ u, (C.M u).L = (C.Mf u).L.comap ((C.incl u).restrictScalars (𝓞 K))

def NuTie (D : D7) (C : ColObj D.what₂.LL D.what₂.Word) (J : ColJoint D.colRec C) : Prop :=
  ∀ u, (D.div.Nu u).L.map ((((J.isoF u).e.toLinearMap).comp (D.nuIn u)).restrictScalars (𝓞 D.what₂.LL)) =
    (C.Npr u).map ((C.incl u).restrictScalars (𝓞 D.what₂.LL))

def DstarTie (d : ColDat) (A : ColArg (Pr := d.Pr) d.W d.Ch) : Prop := d.num.Dstar = (colObj d.W d.Ch d.hX A).Dstar

set_option maxHeartbeats 1000000 in

def concObj (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) : ColObj (d.colRec a).what₂.LL (d.colRec a).what₂.Word :=
  colObj d.W d.Ch d.hX A

def RecJointOf : Prop :=
  ∀ (D : D7) (C : ColObj D.what₂.LL D.what₂.Word) (J : ColJoint D.colRec C), C.InclOk → NuTie D C J → Nonempty (C.RecJoint D)

def ColJointExists : Prop :=
  ∀ (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch), DstarTie d A → 2 * d.X.f * d.R.k < d.Pr.g 0 - 1 →
    d.lev 0 = colLev d.Ch 0 →
    Nonempty (ColJoint (d.colRec a) (concObj d a A))

section Ker

open Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))

theorem twistPrimes_trivialTuple_empty_target : QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime (1 : Chr X.F X.E X.K) = ∅ := by
    ext v
    simp [Qprime]
  show QE sel (1 : Chr X.F X.E X.K) = ∅
  unfold QE
  rw [dif_pos (by rw [h]; exact Set.finite_empty)]
  simp [h]

theorem target_not_mem_qe (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∉ QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) := by
  rw [twistPrimes_trivialTuple_empty_target]
  exact Finset.notMem_empty P

def targetLift {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E n ST SG) :
    DecoF X.E n ST SG (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) :=
  ⟨(p, fun _ => 1), fun P _ => (target_not_mem_qe sel P.1 P.2).elim⟩

def targetCastN {n n' : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (h : n = n') (p : DecoSet X.E n ST SG) :
    DecoSet X.E n' ST SG := h ▸ p

end Ker

section KerRef

open Formalism.L2.Ker Formalism.MainNotions

variable {d : ColDat} (a : ColArgs d) {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 d.X.F) → HeightOneSpectrum (𝓞 d.X.E))

structure KerAmbTied (D : D7) (X : Fields) (σ₀ : X.K →+* ℂ) where
  cc : Ideal (𝓞 D.host.K)
  cc_rec : cc = D.host.ccK
  cc_ok : TaylorLogMetric.IsCurveIdeal D cc
  δ : ℂ
  δ_ok : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ
  B : Base D cc δ
  B_std : B.StdOK
  χ : TaylorLogMetric.IdE D → ℂ
  χ_ok : TaylorLogMetric.IsChi D χ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  idl_ok : TaylorLogMetric.RelDetPinned D idl
  χ_rec : χ = TaylorLogMetric.chiRec D idl
  cD : D.what₂.Tau → ℂ
  cD_ok : IsDgen D cD
  seam : Seam D X
  seam_ok : seam.Ok
  seam_σ : seam.σ₀ = σ₀

def KerAmbTied.amb {D : D7} {X : Fields} {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) : Amb X := ambOf K.seam K.B K.χ K.cD

end KerRef

section Target

open Formalism.L2.GlobalTheoryTheory.ColOpen Formalism.L2.Ker

set_option maxHeartbeats 400000 in

def ColumnsAgreeAt (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) (D : D7) (h : D.colRec = d.colRec a) : Prop :=
  V1.ColHyp d → Nonempty (Formalism.L2.Forms.ColsTied D) ∧
    (Dat.Ok { R := d.R, X := d.X, sig0 := d.σ₀, Pr := d.Pr, Ch := d.Ch, W := d.W, a := A.num.sc.a } →
    Formalism.HermitianLatticesTheory.IsCMUnram d.X.E → MassRatioStd → d.X.f ≤ d.R.k →
    ∀ {Δ : ℝ} {c : d.X.Tau → ℝ} {code : d.Pr.Word → ℕ → ℕ}, Grid (Pr := d.Pr) d.W Δ A.num.Sc c code →
    Ends (Pr := d.Pr) d.W A.num.sc.a A.num.sc.b' A.num.Sc →
    Nodes (Pr := d.Pr) d.W A.num.sc.x A.num.sc.L A.num.eta A.num.Sc → Nums5 d.X d.Pr d.R A.num → NumsZ d.X d.R A.num (logAvC d.X A.num) →
    (∀ u, InWindow d.W d.Ch A.dsig d.num.GamP u) →
    (∀ u, MaxSlopeSummandWithConstant d.W d.Ch u A.num.C0) → ColArgOk d.W d.Ch A →
    ∃ I : ColIface (d.colRec a).what₂.LL (d.colRec a).what₂.Word, I.toColObj = concObj d a A ∧
      ∀ (J : ColJoint D.colRec (ColObj.onRec D h (concObj d a A))), NuTie D (ColObj.onRec D h (concObj d a A)) J →
        Nonempty ((ColObj.onRec D h I.toColObj).RecJoint D) ∧
        ∀ u, ((D.mem u).A.duStar : ℝ) = (ColObj.onRec D h I.toColObj).dstar u ∧
          (D.mem u).A.Xu = (ColObj.onRec D h I.toColObj).Xu u)

def ColumnsAgreeConcrete : Prop :=
  ∀ (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) (D : D7) (h : D.colRec = d.colRec a), ColumnsAgreeAt d a A D h

end Target

end Formalism.L2.Col
end
end

