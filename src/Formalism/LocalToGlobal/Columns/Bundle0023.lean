import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.GFamSEv
import Formalism.LocalToGlobal.Columns.Bundle0022
import Formalism.LocalToGlobal.Columns.Bundle0017
import Formalism.LocalToGlobal.Columns.TiedGlLev

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawExt
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clL_toMatrix_mul {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) :
    LinearMap.toMatrix' κ.toLinearMap * LinearMap.toMatrix' κ.symm.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have : κ.toLinearMap ∘ₗ κ.symm.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.toMatrix'_id]

theorem clL_toMatrix_mul' {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) :
    LinearMap.toMatrix' κ.symm.toLinearMap * LinearMap.toMatrix' κ.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have : κ.symm.toLinearMap ∘ₗ κ.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.toMatrix'_id]

theorem clL_extM_mul {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ciExtM c (LinearMap.toMatrix' κ.toLinearMap) * ciExtM c (LinearMap.toMatrix' κ.symm.toLinearMap) = 1 := by
  rw [← ciExtM_mul, clL_toMatrix_mul, ciExtM_one]

theorem clL_extM_mul' {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ciExtM c (LinearMap.toMatrix' κ.symm.toLinearMap) * ciExtM c (LinearMap.toMatrix' κ.toLinearMap) = 1 := by
  rw [← ciExtM_mul, clL_toMatrix_mul', ciExtM_one]

def clL_ext {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) : Sp E (n + c) ≃ₗ[E] Sp E (n + c) :=
  ciEquiv (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)) (ciExtM c (LinearMap.toMatrix' κ.symm.toLinearMap)) (clL_extM_mul c κ)
    (clL_extM_mul' c κ)

theorem clL_ext_apply {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) :
    clL_ext c κ v = (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)).mulVec v :=
  ciEquiv_apply _ _ _ _ v

theorem clL_ext_inX {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (x : Sp E n) :
    clL_ext c κ (Loc.inX E n c x) = Loc.inX E n c (κ x) := by
  rw [clL_ext_apply, ciExtM_inX]
  congr 1
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem clL_ext_natAdd {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) (i : Fin c) :
    clL_ext c κ v (Fin.natAdd n i) = v (Fin.natAdd n i) := by
  rw [clL_ext_apply, ciExtM_natAdd]

theorem clL_ext_det {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) :
    ((LinearEquiv.det (clL_ext c κ) : Eˣ) : E) = ((LinearEquiv.det κ : Eˣ) : E) := by
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det]
  have h1 : ((clL_ext c κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Sp E (n + c) →ₗ[E] Sp E (n + c)) =
      Matrix.toLin' (ciExtM c (LinearMap.toMatrix' κ.toLinearMap)) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply]
    exact clL_ext_apply c κ v
  rw [h1, LinearMap.det_toLin', ← LinearMap.det_toMatrix' (κ : Sp E n →ₗ[E] Sp E n)]
  unfold ciExtM
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem clL_ext_symm {n : ℕ} (c : ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) : (clL_ext c κ).symm = clL_ext c κ.symm := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.symm_apply_eq, clL_ext_apply, clL_ext_apply, Matrix.mulVec_mulVec, ← ciExtM_mul, clL_toMatrix_mul, ciExtM_one,
    Matrix.one_mulVec]

end Ext

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecordFS
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Fam

variable {X : Fields} {R : Ranks}

abbrev FamStabS (F : GFamS X.K) (c : F.Cl) : Type := MulAction.stabilizer (F.G c.1) ((F.sec c.1).rep c.2)

def recChainFS (hc : X.Tau → HCParam R) (F : ℕ → GFamS X.K) (hF : ∀ j, (F j).Ok) (σ₀ : X.K →+* ℂ)
    (D : ℕ) (hD : 0 < D) (hdvd : ∀ j, j ≤ R.m → ∀ c : (F j).Cl, Nat.card (FamStabS (F j) c) ∣ D)
    (A : ChainArgF R (fun i => (F i).toGFam) σ₀) : ColumnChain R X.Tau hc where
  cls := fun i => (F i).Cl
  clsFin := fun i => (hF i).fintypeCl
  stab := fun i c => FamStabS (F i) c
  stabGrp := fun _ _ => inferInstance
  stabFin := fun i c => (hF i c.1).fin_stab _
  DGam := D
  DGam_pos := hD
  dvd_DGam := hdvd
  Y := fun i => FrS X σ₀ (R.N i)
  de := fun _ y τ => deFr y τ
  de_ne := fun _ y τ => (y.2 τ).ne_zero
  rhoDet := A.rhoDet
  rhoDet' := A.rhoDet'
  rho_norm := A.rho_norm
  rho'_norm := A.rho'_norm
  unf := A.unf
  sSharp := sSharpH hc
  sSharp_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (hc τ) ⟨i, h⟩).2
    have e : (RowPar.of (hc τ)).eAt i = (hc τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dif_pos h]
      rfl
    unfold sSharpH
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]
  sDiv := sDivH hc
  sDiv_eq := fun i h τ => by
    obtain ⟨a, ha⟩ := (rec_sInt R (hc τ) ⟨i, h⟩).1
    have e : (RowPar.of (hc τ)).eAt i = (hc τ).e ⟨i, h⟩ := by
      unfold RowPar.eAt
      rw [dif_pos h]
      rfl
    unfold sDivH
    rw [e]
    simp only at ha
    rw [ha, Int.floor_intCast]

end Fam

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCls
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure StepCrd {X : Fields} (Pr : Primes X) (σ₀ : X.K →+* ℂ) (n : ℕ) {cls : Type}
    (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  J : Matrix (Fin n) (Fin n) X.E
  f : ℕ
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  emb : X.Tau → X.E →+* ℂ
  lat : cls → Submodule (𝓞 X.E) (Fin n → X.E)
  l0 : Submodule (𝓞 X.E) (Fin n → X.E)
  hJ : J = 1
  hf : f = X.f
  hbad : bad = plUnder X.F Pr.vGs
  hemb : emb = X.embC σ₀
  hlat : lat = L
  hl0 : l0 = stdLat X.E n

def StepCrd.std {X : Fields} (Pr : Primes X) (σ₀ : X.K →+* ℂ) (n : ℕ) {cls : Type}
    (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) : StepCrd Pr σ₀ n L :=
  ⟨1, X.f, plUnder X.F Pr.vGs, X.embC σ₀, L, stdLat X.E n, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure ClsG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E σ J T f bad
  y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Formalism.L2.Forms.Cls lev))
  y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb
  stabI : ∀ c, stab c →* UJ (σ : E →+* E) J
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (y c).1).toMonoidHom

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def tieLev : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (fun w => (Λ w).H) (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = Pr.T u)) (rls_T_notUnder hPr u)
    (colBase_index hc n hPr u) ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

def clsG₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  y := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y
  y_bij := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y_bij
  y_lat := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y_lat
  stabI := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI
  stabI_inj := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI_range c γ.1 γ.2

def clsG (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) :
    ClsG hc.sig Q.J (Pr.T u) Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsG₁ hc hX hPr σ₀ u Λ c₀ s hS hs

theorem clsG_std (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) :
    clsG hc hX hPr σ₀ u Λ c₀ s hS hs (StepCrd.std Pr σ₀ n _) = clsG₁ hc hX hPr σ₀ u Λ c₀ s hS hs := rfl

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem badG_eq : CF.badG (d.colRec a) = plUnder d.X.F d.Pr.vGs := by
  classical
  have key : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)), v ∈ plUnder d.X.F (d.Pr.vG i) ↔ (d.Pr.g i : 𝓞 d.X.F) ∈ v.asIdeal := by
    intro i v
    have h0 : d.X.conjO (d.Pr.piG i) ≠ 0 := by
      intro h
      have h1 := d.hPr.piG_norm i
      rw [h, mul_zero] at h1
      exact (Nat.cast_ne_zero.2 (d.hPr.g_prime i).ne_zero) h1.symm
    refine mem_plUnder_iff_norm d.sp.cm (fun P => mem_divs h0 P) (d.Pr.g i) ?_ v
    have h2 : cO d.X.E (d.X.conjO (d.Pr.piG i)) = d.Pr.piG i := cO_cO _
    rw [h2, mul_comm]
    exact d.hPr.piG_norm i
  ext v
  show ((d.Pr.g 0 : 𝓞 d.X.F) ∈ v.asIdeal ∨ (d.Pr.g 1 : 𝓞 d.X.F) ∈ v.asIdeal) ↔ _
  rw [← key 0, ← key 1]
  constructor
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, h⟩
    · exact ⟨P, Finset.mem_union_right _ hP, h⟩
  · rintro ⟨P, hP, h⟩
    rcases Finset.mem_union.1 hP with h' | h'
    · exact Or.inl ⟨P, h', h⟩
    · exact Or.inr ⟨P, h', h⟩

theorem selfDualLatticeCoords_eq_std (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : CF.selfDualLatticeCoords (d.colRec a) i hi = stdLat d.X.E (d.R.N i) := by
  show (d.sp.X i).L0.map (((d.crd i hi : (d.sp.X i).V ≃ₗ[d.host.E] (Fin (d.R.N i) → d.host.E)) :
    (d.sp.X i).V →ₗ[d.host.E] (Fin (d.R.N i) → d.host.E)).restrictScalars (𝓞 d.host.E)) = _
  rw [hS.selfDual_span_frame_X i hi, Submodule.map_span, ← Set.range_comp]
  have hfr : ∀ b, (d.crd i hi) ((d.sp.X i).frame b) = Pi.single (finCongr (d.sp.X_rank i hi) b) (1 : d.host.E) := by
    intro b
    funext j
    show (d.sp.X i).frame.equivFun ((d.sp.X i).frame b) ((finCongr (d.sp.X_rank i hi)).symm j) = _
    rw [Basis.equivFun_self, Pi.single_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    show (d.crd i hi) ((d.sp.X i).frame b) ∈ _
    rw [hfr]
    intro j _
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.one_le.1 le_rfl
    · exact zero_mem _
  · intro x hx
    have hx' : ∀ j, ∃ r : 𝓞 d.host.E, algebraMap (𝓞 d.host.E) d.host.E r = x j := fun j =>
      Submodule.mem_one.1 (hx j trivial)
    choose r hr using hx'
    have hsum : x = ∑ j, r j • (d.crd i hi) ((d.sp.X i).frame ((finCongr (d.sp.X_rank i hi)).symm j)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [hfr, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, hr]
      · intro j _ hj
        rw [hfr, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

def stepCrd (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    StepCrd d.Pr d.σ₀ (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  J := CF.gramN (d.colRec a) i hi
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := CF.clsCrd (d.colRec a) u i hi
  l0 := CF.selfDualLatticeCoords (d.colRec a) i hi
  hJ := gramN_eq a hS i hi
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := funext fun c => clsCrd_eq a u i hi c
  hl0 := selfDualLatticeCoords_eq_std a hS i hi

def PtSurj (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), DecoPtSurj d.sp.cm (d.R.N i) (d.Pr.vT u) d.Pr.vGs

def stepClsG (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  clsG d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi)

def classAgreement (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.ClsTied (D := d.colRec a) u i hi where
  lev := (stepClsG a hS hH hP u i hi).lev
  y := (stepClsG a hS hH hP u i hi).y
  y_bij := (stepClsG a hS hH hP u i hi).y_bij
  y_lat := (stepClsG a hS hH hP u i hi).y_lat
  stabI := (stepClsG a hS hH hP u i hi).stabI
  stabI_inj := (stepClsG a hS hH hP u i hi).stabI_inj
  stabI_range := (stepClsG a hS hH hP u i hi).stabI_range

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGl
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section Prod

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

include hc hPr in
theorem glk_under_mem (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) : (Pr.g i : 𝓞 X.F) ∈ (underPl X.F w).asIdeal :=
  (glk_under hc hPr i _).1 ⟨w, hw, rfl⟩

theorem glk_gwOf_under (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) :
    gwOf hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) = ⟨w, glk_vG_le i hw⟩ :=
  (gwOf_uniq hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) ⟨w, glk_vG_le i hw⟩
    (show (underPl X.F w).asIdeal = _ from rfl)).symm

open Classical in
theorem glk_prod_i (A : Pr.vGs → ℂ) (i : Fin 2) :
    ∏ w ∈ Pr.vG i, (if h : w ∈ Pr.vGs then A ⟨w, h⟩ else 1) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h) := by
  have h1 : ∀ v : HeightOneSpectrum (𝓞 X.F), (∏ᶠ (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h)) =
      if h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal then A (gwOf hc hPr i v h) else 1 := fun v => finprod_eq_dif _
  rw [finprod_congr h1]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (Pr.vG i).image (underPl X.F))]
  · rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun w hw => ?_
      rw [dif_pos (glk_vG_le i hw), dif_pos (glk_under_mem hc hPr i hw), glk_gwOf_under hc hPr i hw]
    · intro w hw w' hw' e
      have e1 := glk_gwOf_under hc hPr i hw
      have e2 := glk_gwOf_under hc hPr i hw'
      have e3 : gwOf hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) =
          gwOf hc hPr i (underPl X.F w') (glk_under_mem hc hPr i hw') := by
        congr 1
      rw [e1, e2] at e3
      exact congrArg Subtype.val e3
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    have hp : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
      by_contra hn
      exact hv (dif_neg hn)
    rw [Finset.coe_image]
    refine ⟨(gwOf hc hPr i v hp).1, gwOf_mem hc hPr i v hp, ?_⟩
    exact HeightOneSpectrum.ext (gwOf_over hc hPr i v hp).symm

theorem glk_prod (A : Pr.vGs → ℂ) :
    ∏ w : Pr.vGs, A w =
      ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h) := by
  classical
  have h0 : ∏ w : Pr.vGs, A w = ∏ w ∈ Pr.vGs, (if h : w ∈ Pr.vGs then A ⟨w, h⟩ else 1) := by
    rw [← Finset.prod_coe_sort Pr.vGs]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [dif_pos w.2]
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    exact hPr.g_ne ((hPr.vG_norm 0 w h0).symm.trans (hPr.vG_norm 1 w h1))
  rw [h0, Fin.prod_univ_two, ← glk_prod_i hc hPr A 0, ← glk_prod_i hc hPr A 1]
  unfold Primes.vGs
  convert Finset.prod_union hd using 2

end Prod

section GLc

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ)

def tieGLoc (hCh : Ch.Ok) : Formalism.L2.Forms.GLoc X.F X.E hc.sig Pr.g where
  sp := S.sp
  sp_sig := S.sp_sig
  sp_alg := S.sp_alg
  piG := Pr.piG
  piG_norm i := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    rw [map_mul, map_natCast] at this
    exact this
  sp_pi := S.sp_pi
  psi0 i v h := glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h))
  psi_zero_nontrivial_character i v h := by
    intro h1
    apply hCh.psi_zero_nontrivial_character (gwOf hc hPr i v h)
    ext x
    have h2 := DFunLike.congr_fun h1 (S.eK hPr i v h x)
    rw [glmPsi_apply, AddChar.one_apply] at h2
    rw [AddChar.one_apply]
    exact σ₀.injective (h2.trans (map_one σ₀).symm)
  chiB i v h s := glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)

end GLc

end Formalism.L2.Col
end
end

