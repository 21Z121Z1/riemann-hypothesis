import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.LocalToGlobal.Columns.Bundle0036
import Formalism.LocalToGlobal.Columns.Bundle0022
import Formalism.LocalToGlobal.Columns.Bundle0034
import Formalism.LocalToGlobal.Columns.Bundle0035
import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DetChrOf
import Formalism.LocalToGlobal.Columns.RecLevelLocF
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.Bundle0026

-- bundled from Formalism.LocalToGlobal.Columns.ChainOneP
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem oneYbSym {m2 : ℕ} (hc' : cOf R m2 = 1) (hc : cOf R (m2 + 1) = 0) (hs : cst.sharp = true) : OneYbSym Ch sel mu cst m2 :=
  fun P hP x₀ y' h l => psiAt_sym Ch sel mu cst hc' hc hs P hP x₀ y' h l

theorem oneYbSym_of_m {m2 : ℕ} (hm : R.m = m2 + 2) (hs : cst.sharp = true) : OneYbSym Ch sel mu cst m2 :=
  oneYbSym Ch sel mu cst (by unfold cOf; omega) (by unfold cOf; omega) hs

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.CoordLatticeSelfDualAuxiliary
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d)

theorem gram_eq_one_of_standard (hS : SpStd d.toColBase) : d.sp.X'.gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show d.sp.X'.hT (d.sp.X'.frame x) (d.sp.X'.frame y) = _
  rw [hS.P_on, Matrix.one_apply]

theorem coordLattice_selfDual_auxiliary (hS : SpStd d.toColBase) : Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0 = stdLat d.X.E d.sp.X'.rank := by
  unfold Formalism.L2.Herm.crdLat
  rw [hS.selfDual_span_frame_auxiliary]
  refine th_map_span_std (Formalism.L2.Herm.crd d.sp.X') _ (Equiv.refl _) fun a => ?_
  funext j
  show d.sp.X'.frame.equivFun (d.sp.X'.frame a) j = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext eq_comm

theorem hp_crdLat_map (L : Submodule (𝓞 d.host.E) (Fin (d.R.N d.R.m - 1) → d.host.E)) :
    Formalism.L2.Herm.crdLat d.sp.X' (L.map (((CF.crdP (d.colRec a)).symm :
      (Fin (d.R.N d.R.m - 1) → d.host.E) →ₗ[d.host.E] d.sp.X'.V).restrictScalars (𝓞 d.host.E))) =
      Formalism.L2.Forms.reL (CF.rankP (d.colRec a)).symm L := by
  unfold Formalism.L2.Herm.crdLat Formalism.L2.Forms.reL
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.X'.frame.equivFun ((CF.crdP (d.colRec a)).symm x) j = _
  unfold CF.crdP
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrdP (u : d.what₂.Word) : HCrdP d.X (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  n' := d.sp.X'.rank
  hn := CF.rankP (d.colRec a)
  J := d.sp.X'.gram
  hJ := gram_eq_one_of_standard hS
  l0 := Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0
  hl0 := by rw [hp_baseLb_empty, th_reL_std, coordLattice_selfDual_auxiliary hS]
  lat := fun c => Formalism.L2.Herm.crdLat d.sp.X' (hqLatP (parabolicClassAgreement a hS hH hP u) c)
  hlat := fun c => hp_crdLat_map a _

def hermPackP (u : d.what₂.Word) :=
  levPackP d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (hCrdP a hS hH hP u)

set_option maxHeartbeats 4000000 in

def levelExponentAtT (u : d.what₂.Word) : AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) :=
  xpOf (tildeLatticeAgreement a hS hH hP u)
    (LevPackP.toStep (S := d.sp.X') (lat := hqLatP (parabolicClassAgreement a hS hH hP u)) (hermPackP a hS hH hP u))
    (LevPackP.toCls (S := d.sp.X') (lat := hqLatP (parabolicClassAgreement a hS hH hP u)) (hermPackP a hS hH hP u))

theorem th_carP (u : d.what₂.Word) :
    Formalism.L2.Forms.SameCar (CF.rankP (d.colRec a)) (Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0) (parabolicClassAgreement a hS hH hP u).lev.Lb
      (levelExponentAtT a hS hH hP u).levP.Uloc (parabolicClassAgreement a hS hH hP u).lev.Uloc
      (levelExponentAtT a hS hH hP u).levP.U (parabolicClassAgreement a hS hH hP u).lev.U
      (fun c => ((levelExponentAtT a hS hH hP u).clsP.y c).1) (fun c => ((parabolicClassAgreement a hS hH hP u).y c).1)
      (fun c t => ((levelExponentAtT a hS hH hP u).clsP.stabI c t).1) (fun c t => ((parabolicClassAgreement a hS hH hP u).stabI c t).1) :=
  levelPacking_sameCarrier d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP _ (hCrdP a hS hH hP u) (crdPr a hS hH)

theorem th_latP (u : d.what₂.Word) (c : PCl d) :
    (parabolicClassAgreement a hS hH hP u).lat c = ((levelExponentAtT a hS hH hP u).lattice₂ c).map
      ((CF.crdP (d.colRec a) : d.sp.X'.V →ₗ[d.host.E] (Fin (d.R.N d.R.m - 1) → d.host.E)).restrictScalars (𝓞 d.host.E)) :=
  hqLatP_crd (parabolicClassAgreement a hS hH hP u) c

theorem joint_lastVector (u : d.what₂.Word) :
    (tildeLatticeAgreement a hS hH hP u).z0 = CF.crdN (d.colRec a) d.R.m le_rfl (levelExponentAtT a hS hH hP u).z0 :=
  lastVector_coords (tildeLatticeAgreement a hS hH hP u)

theorem th_ga (u : d.what₂.Word) (c : PCl d) :
    ((tildeLatticeAgreement a hS hH hP u).ga c).1 = Formalism.L2.Forms.reGL (CF.rankN (d.colRec a) d.R.m le_rfl) _
      (Formalism.L2.Herm.toGLb (d.sp.X d.R.m).frame ((levelExponentAtT a hS hH hP u).tilG c).1) :=
  (hqG_re d.R.m le_rfl ((tildeLatticeAgreement a hS hH hP u).ga c)).symm

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DetChrOfChi
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace Formalism.L2.Col

namespace DetChrOf

section Pull

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K]

def chiPull (σ : E →ₐ[F] E) (c : Formalism.L2.DIV.Chr F E K) : Formalism.L2.DIV.Chr F E K := c.comp (Formalism.L2.DIV.h90 σ)

end Pull

section Comparison₂

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

theorem chiDetTie_of_pt (σ₀ : X.K →+* ℂ) (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (Am : Formalism.L2.Ker.Amb X)
    (u : Pr.Word) (f : ∀ a : ℕ, Submodule (𝓞 X.E) (Sp X.E a) → ℂ)
    (hF : ∀ a b N N', Am.chiF a b N N' = f a N ^ (((b / 2 : ℕ) : ℤ)) * f b N' ^ (-((a / 2 : ℕ) : ℤ)))
    (hpt : ∀ j (cl : StCl W Λ u j), σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) =
      f (R.N j) (repN W Λ u j cl)) :
    ChiDetTie W Λ σ₀ Dc hc Am u := by
  intro i _ c c'
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, map_zpow₀, hpt, hpt, hF]
  have ha : f (R.N i) (repN W Λ u i c) ≠ 0 := by
    rw [← hpt]; exact (map_ne_zero σ₀).mpr (Units.ne_zero _)
  have hb : f (R.N (i + 1)) (repN W Λ u (i + 1) c') ≠ 0 := by
    rw [← hpt]; exact (map_ne_zero σ₀).mpr (Units.ne_zero _)
  rw [zpow_neg, zpow_neg]
  field_simp

end Comparison₂

section Amb

open Formalism.L2.Ker

variable {D : D7} {X : Fields} (s : Seam D X)

end Amb

end DetChrOf

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LevPackFrLat
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem th_fLoc_pi (h : BasePi ST π) (a : Formalism.BasicNotions.intV E v)
    (ha : (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π)) (m : fMod hc n ST v) :
    a • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  show a • fLoc hc n ST v x = 0
  rw [← map_smul, rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (algebraMap (𝓞 E) E π))) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  refine ⟨fun i hi => mul_mem a.2 (hx.1 i hi), ?_⟩
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) *
    ((a : E ⊗[F] v.adicCompletion F) * x.1 (lastIdx n)) ∈ Formalism.BasicNotions.intV E v
  rw [ha, rll_cp_mul v h]
  exact hx.2

end Loc

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

theorem levPack_fM_pi (H : HCrd Pr n fun c => (s c).1.L) (v : HeightOneSpectrum (𝓞 X.F)) (hv : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal)
    (a : intV X.E v) (ha : (a : X.E ⊗[X.F] v.adicCompletion X.F) = inclE (F := X.F) (v.adicCompletion X.F) (Pr.piT u : X.E))
    (m : (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fM v hv) : a • m = 0 := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_fLoc_pi hc _ v (basePi_of_ok hX hPr u) a ha m

theorem levPack_frLat (S : GSplit (Pr := Pr) hc) (H : HCrd Pr n fun c => (s c).1.L) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F))
    (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) (t : Fin H.n' → v.adicCompletion X.F) :
    (∃ x ∈ Formalism.L2.Herm.locL v (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb, ∀ b, (S.sp i v h (x b)).1 = t b) ↔
      ∀ b, (((1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ : GL (Fin H.n') (v.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (v.adicCompletion X.F)).mulVec t b ∈ v.adicCompletionIntegers X.F := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  refine gco_fr_lat _ (Pr.vT u) v (S.sp i v h) (S.sp_alg i v h) ?_ t
  intro hT
  have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
    (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
  exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl h; exact Or.inr h))

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MuDetOfLoc
section
open NumberField IsDedekindDomain Module
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure DetChr.Loc (Dc : DetChr X R.m) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.E →ₐ[X.F] X.E) : Prop where
  trivF : ∀ i, i < R.m → (Formalism.L2.DIV.h90 σ).ker ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  unr : ∀ i, i < R.m → ∀ y ∈ intU X.F X.E,
    (∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal → Units.map (Formalism.UG.prV (E := X.E) v).toMonoidHom y = 1) →
    (Dc.muAt i * (mu : Chr X.F X.E X.K)) y = 1
  unif : ∀ i, i < R.m → ∀ P : HeightOneSpectrum (𝓞 X.E),
    (¬ ∃ P' ∈ rowSG Pr sel mu, P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)) →
    IsUnifVal (Dc.muAt i * (mu : Chr X.F X.E X.K)) P (mUof Ch mu i P)⁻¹
  tame : ∀ i, i < R.m → ∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    wildAt X.E v ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  res : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu,
    IsResChar (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1
      (open Classical in if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1)
  atq : ∀ i, i < R.m → ∀ (P : rowSG Pr sel mu) (k : X.Kˣ), IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k →
    cst.muq (i + 1) P = ((k⁻¹ : X.Kˣ) : X.K)
  atq_ex : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu, ∃ k : X.Kˣ, IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k
  trivChi : (Formalism.L2.DIV.h90 σ).ker ≤ Dc.chi.ker
  unrChi : ∀ y ∈ intU X.F X.E, Dc.chi y = 1

def PtSurjAll (hc : Formalism.BasicNotions.CMData X.F X.E) (Pr : Primes X) (R : Ranks) (u : Pr.Word) : Prop :=
  ∀ n, n ≤ R.m → ∀ p : DecoSet X.E (R.N n) (Pr.vT u) Pr.vGs,
    letI : NeZero (R.N n) := ⟨(R.N_pos n).ne'⟩
    decoOf (Pr.vT u) Pr.vGs (ptOf hc (R.N n) (Pr.vT u) Pr.vGs p : GL (Fin (R.N n)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) = p

def MuDetOfLoc : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (u : Pr.Word),
    X.Ok → Pr.Ok → (∀ v, (sel v).asIdeal.under (𝓞 X.F) = v.asIdeal) → Dc.Loc Ch sel (mu0 X.F X.E X.K S) cst hc.sig → PtSurjAll hc Pr R u →
    ∀ i, i < R.m → ∀ n, (n = i ∨ n = i + 1) → ∀ p : DecoSet X.E (R.N n) (Pr.vT u) Pr.vGs,
      letI : NeZero (R.N n) := ⟨(R.N_pos n).ne'⟩
      (((Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
          (ptOf hc (R.N n) (Pr.vT u) Pr.vGs p : GL (Fin (R.N n)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ : X.Kˣ) : X.K) =
        muInvDet sel (rowSG Pr sel (mu0 X.F X.E X.K S)) (mUof Ch (mu0 X.F X.E X.K S) i) (muAt Ch sel (mu0 X.F X.E X.K S) cst i) p.1.N
          (frsD sel (mu0 X.F X.E X.K S) p)

end Loc

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecChainYUnfPol
section
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def cplAt (u : Pr.Word) (m2 j : ℕ) (b : L.β j) : Cpl ((chF W sel mu L u j).mem b) where
  Yb := Set (Sp X.E (R.N j))
  actY :=
    { smul := fun g Y => (fun v => g.1.1 v) '' Y
      one_smul := fun Y => Set.image_id Y
      mul_smul := fun g h Y => (Set.image_image (fun v => g.1.1 v) (fun v => h.1.1 v) Y).symm }
  ys p := if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  fin p := by
    split_ifs
    · exact ybSet_finite sel mu cst _ p.deco.2.lat.fg
    · exact Set.finite_singleton _
  equiv g p Y := by
    split_ifs
    · exact ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y
    · show (fun v => g.1.1 v) '' Y = Set.univ ↔ Y = Set.univ
      constructor
      · intro h
        have h2 : (fun v => g.1.1 v) '' Y = (fun v => g.1.1 v) '' Set.univ := by
          rw [h, Set.image_univ]
          exact (g.1.1.surjective.range_eq).symm
        exact g.1.1.injective.image_injective h2
      · rintro rfl
        rw [Set.image_univ]
        exact g.1.1.surjective.range_eq

@[reducible] def chFY (u : Pr.Word) (m2 j : ℕ) : GFam X.K where
  β := L.β j
  V := (colValF W sel mu u j).V
  ιV := VVIdx (colValF W sel mu u j).lam
  bV := (colValF W sel mu u j).bV
  pair := (colValF W sel mu u j).pair
  G b := FrmG (L.levG j b) (L.levQ j b)
  D b := (cplAt W sel mu cst L u m2 j b).Pts
  actD b := (cplGSD (cplAt W sel mu cst L u m2 j b)).actD
  ρ b := frmRho (colValF W sel mu u j) (L.levG j b) (L.levQ j b)
  Nab _ p := (colValF W sel mu u j).Nab p.1.1
  Del _ p := (colValF W sel mu u j).Del p.1.1

variable {W sel mu cst L}

def ptYc {u : Pr.Word} {m2 j : ℕ} (c : (chFY W sel mu cst L u m2 j).Cl) : ChPt (R := R) sel mu u j :=
  (((chFY W sel mu cst L u m2 j).mem c.1).outSec.rep c.2).1.1

def ybY {u : Pr.Word} {m2 j : ℕ} (c : (chFY W sel mu cst L u m2 j).Cl) : Set (Sp X.E (R.N j)) :=
  (((chFY W sel mu cst L u m2 j).mem c.1).outSec.rep c.2).1.2

def XiY {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl)
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i < m2 then XiEntry Ch sel mu cst L i c.1 c'.1 (ptYc c) (ptYc c') x
  else if i = m2 then XiCpl1 Ch sel mu cst L i c.1 (ptYc c) (ptYc c') (ybY c') x
  else if i = m2 + 1 then XiTop Ch sel mu cst i (ptYc c) (ybY c) (ptYc c') x
  else 0

def thY (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl) :
    VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (ptYc c).deco.1.N (ptYc c').deco.1.N (XiY Ch i c c')

def kerYc (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u (i + 1)) :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    (ptYc c).deco.1.N (frsF sel mu (ptYc c)) (ptYc c').deco.1.N (frsF sel mu (ptYc c')) (XiY Ch i c c')

def rhoY (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) : ℂ :=
  σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c).deco.1.N (frsF sel mu (ptYc c))) *
    (Am.chiF (R.N i) (R.N (i + 1)) (ptYc c).deco.1.N (stdLat X.E (R.N (i + 1))))⁻¹

def rhoY' (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl) : ℂ :=
  (σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c').deco.1.N (frsF sel mu (ptYc c'))))⁻¹ *
    (Am.chiF (R.N i) (R.N (i + 1)) (stdLat X.E (R.N i)) (ptYc c').deco.1.N)⁻¹

def RhoYUnit (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) : Prop :=
  (∀ i, i < R.m → ∀ c : (chFY W sel mu cst L u m2 i).Cl, ‖rhoY Ch σ₀ Am i c‖ = 1) ∧
    ∀ i, i < R.m → ∀ c' : (chFY W sel mu cst L u m2 (i + 1)).Cl, ‖rhoY' Ch σ₀ Am i c'‖ = 1

def _root_.Formalism.L2.Ker.Amb.ChiSplit (Am : Amb X) (a b : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    Am.chiF a b N N' = Am.chiF a b N (stdLat X.E b) * Am.chiF a b (stdLat X.E a) N'

def ChainArgF.ofChKer (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2) :
    ChainArgF R (chFY W sel mu cst L u m2) σ₀ where
  rhoDet := rhoY Ch σ₀ Am
  rhoDet' := rhoY' Ch σ₀ Am
  rho_norm := hU.1
  rho'_norm := hU.2
  unf i c c' := unfTh σ₀ Am.cD (thY Ch Am i c c')

def recChainY (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2)
    (hF : ∀ j, (chFY W sel mu cst L u m2 j).Ok) (D : ℕ) (hD : 0 < D)
    (hdvd : ∀ j, j ≤ R.m → ∀ c : (chFY W sel mu cst L u m2 j).Cl, Nat.card (FamStab (chFY W sel mu cst L u m2 j) c) ∣ D) :
    ColumnChain R X.Tau (W.hc u) :=
  recChainF (W.hc u) (chFY W sel mu cst L u m2) hF σ₀ D hD hdvd (ChainArgF.ofChKer Ch σ₀ Am u m2 hU)

variable {Ch}

end Charts

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RefXi1Above
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Ref1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)

def refXi1 : XiFam Pr R u := fun i p p' x => XiRef Ch sel mu cst L m2 al i (liftQ hQ p) (liftQ hQ p') x

theorem refXi1_above (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m ≤ i) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs)
    (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    refXi1 Ch sel mu cst L hQ m2 al u i p p' x = 0 := by
  unfold refXi1 XiRef
  rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]

def refArg1 {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hm : R.m = m2 + 2) (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
    (H : XiHyp W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u) G) : ChainArg W Λ G u :=
  ChainArg.ofXi hE { H with above := fun i hi p p' x => refXi1_above Ch sel mu cst L hQ m2 al u hm i hi p p' x }

end Ref1

end Formalism.L2.Col
end
end

