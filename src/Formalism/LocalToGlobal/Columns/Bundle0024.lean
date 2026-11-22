import Formalism.LocalToGlobal.Columns.Bundle0023
import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalToGlobal.HermitianForms.Bundle0005
import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
import Formalism.LocalToGlobal.Columns.Bundle0020
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.TiedGlSplit
import Formalism.LocalToGlobal.Columns.TwQDefs

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawXiStmt
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section XiE1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def FirstUnfoldingJInvarianceLaw (i : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (κ : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (κ' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))),
    κ ∈ GLint X.E (R.N i) P.1 → κ' ∈ GLint X.E (R.N (i + 1)) P.1 →
    clL_ext (cOf R i) κ ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N i) (cOf R i) →
    clL_ext (cOf R (i + 1)) κ' ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N (i + 1)) (cOf R (i + 1)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      E1at Ch sel mu cst i P 1 1 (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) =
        LocE.lamGBS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.r R.t (i + 1) (R.N (i + 1)) (cOf R (i + 1))
            (clL_ext (cOf R (i + 1)) κ'.symm).toLinearMap *
          (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ'.symm : X.Eˣ) : X.E))⁻¹ *
          (LocE.lamGBS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.r R.t i (R.N i) (cOf R i) (clL_ext (cOf R i) κ).toLinearMap *
            (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ : X.Eˣ) : X.E))⁻¹) *
          E1at Ch sel mu cst i P 1 1 y

def XiTgtLaw (i : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ κ' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1)), κ' ∈ GLint X.E (R.N (i + 1)) P.1 →
    clL_ext (cOf R (i + 1)) κ' ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N (i + 1)) (cOf R (i + 1)) →
    ∀ w : HomE X.E (R.N i) (R.N (i + 1)),
      Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B)
          (((qOf P.1 : X.K) ^ cst.B)⁻¹) (PhiAt Ch mu cst.sharp i P.1) (κ'.symm.toLinearMap ∘ₗ w) =
        Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B)
          (((qOf P.1 : X.K) ^ cst.B)⁻¹)
          (fun x => PhiAt Ch mu cst.sharp i P.1 ((clL_ext (cOf R (i + 1)) κ'.symm).toLinearMap ∘ₗ x)) w

end XiE1

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HCrd {X : Fields} (Pr : Primes X) (n : ℕ) {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  f : ℕ
  hf : f = X.f
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  hbad : bad = plUnder X.F Pr.vGs
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPack {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad
  cls : RecCls hc J lev.Lb lev.U stab lat
  bad_iff : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ bad ↔ ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v lev.Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v lev.Lb, ∃ z ∈ Formalism.L2.Herm.locL v lev.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ lev.Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ lev.Uloc v ↔
    (x ∈ levelVL hc.sig J v lev.Lb ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J lev.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v lev.Lb)

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def LocalLevelIsKOneAtT : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (Pr.T u : 𝓞 X.F) ∈ v.asIdeal → ∀ x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F),
    x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
    (x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) X.E) v (baseLb X.E n (Pr.vT u)) ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 X.E)
          (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)))),
        (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb X.E n (Pr.vT u)))

include hc hPr in

theorem th_plUnder_vGs (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ ((Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal) := by
  classical
  have key : ∀ (i : Fin 2), v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
    intro i
    have h0 : X.conjO (Pr.piG i) ≠ 0 := by
      intro h
      have h1 := hPr.piG_norm i
      rw [h, mul_zero] at h1
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs h0 P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
    rw [h2, mul_comm]
    exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, h⟩
    rcases Finset.mem_union.1 hP with h' | h'
    · exact Or.inl ⟨P, h', h⟩
    · exact Or.inr ⟨P, h', h⟩
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, h⟩
    · exact ⟨P, Finset.mem_union_right _ hP, h⟩

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

def levPack₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) :
    LevPack hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  cls := recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs
  bad_iff := th_plUnder_vGs hc hPr
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n (Pr.vT u) Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · intro hT
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
        (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
      exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl hv; exact Or.inr hv))
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  UlocAlt := hK

def levPack (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) :
    LevPack hc H.n' H.J Pr.g (Pr.T u) H.f H.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPack₁ hc hX hPr σ₀ u Λ c₀ s hS hs hK

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPack.toStep (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel hc S gp T f where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := fun x hx => Submodule.subset_span (P.lev.Lb_int x hx)
  Lb_dual := fun y hy => by
    refine Submodule.span_induction (p := fun y _ => (T : E) • y ∈ P.lev.Lb) (fun y hy => P.lev.Lb_dual y hy) ?_ ?_ ?_ hy
    · rw [smul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  Uloc_g := P.Uloc_g
  UlocAlt := P.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq

def LevPack.toCls (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S P.toStep.Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem max_slope_twisted_lattice (hS : FockSubNorm) (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (g : ι → GL (Fin n) K)
    (hg : ∀ τ, ∀ x ∈ M τ, ∀ a, ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈ (1 : Submodule (𝓞 K) K))
    (hpos : ∀ v τ, 0 < gN K g v τ)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0) (hI : (I : Submodule (𝓞 K) K) = twId lam M)
    (c0 : ℝ) (hc0 : 0 < c0) (hc : ∀ m, c0 ≤ monW lam m) :
    (tenH K lam M).muMax ≤ -Real.log c0 - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
      + ∑ τ, (dW (lam τ) : ℝ) * ((1 / (nPl K : ℝ)) * ∑ v, Real.log (gN K g v τ)) := by
  have hΔ : Submodule.IsLattice K (delK lam M) := (nabDelLattice K ι n lam M hM).2
  have hA0 : delK lam M ≠ ⊥ := isLattice_ne_bot hΔ
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
  have hinj := cfMap_injective lam g
  have hφx0 : cfMap lam g x0 ≠ 0 := fun h => hx00 (hinj (by rw [h, map_zero]))
  have hne : cfMap lam g ≠ 0 := fun h => hφx0 (by rw [h]; rfl)
  have hNE : Nonempty (MonI lam) := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hφx0 (funext fun m => hE.elim m)
  have hX : ∀ v, IsUnit ((tenH K lam M).X v).det :=
    (formH_spec (bVV K lam) (pairK lam fun _ => 1) (tensor_pairing_pos_def K lam) (delK lam M)).1
  have hX' : ∀ v : InfinitePlace K, IsUnit ((monD lam)⁻¹).det := fun _ => Matrix.isUnit_nonsing_inv_det _ (monD_det lam)
  set L0 : Submodule (𝓞 K) (MonI lam → K) := ⨆ m : MonI lam, Submodule.span (𝓞 K) ({Pi.single m 1} : Set (MonI lam → K)) with hL0
  have hL0fg : L0.FG := by
    have : L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), Submodule.span (𝓞 K) ({Pi.single m 1} : Set (MonI lam → K)) := by simp [hL0]
    rw [this]
    exact Submodule.fg_biSup _ _ fun m _ => Submodule.fg_span (Set.finite_singleton _)
  have hsingle : ∀ m : MonI lam, (Pi.single m 1 : MonI lam → K) ∈ L0 := fun m =>
    (le_iSup (fun m : MonI lam => Submodule.span (𝓞 K) ({Pi.single m 1} : Set (MonI lam → K))) m) (Submodule.mem_span_singleton_self _)
  have hsne : ∀ m : MonI lam, (Pi.single m 1 : MonI lam → K) ≠ 0 := fun m h => by
    have := congrFun h m
    simp at this
  have hL00 : L0 ≠ ⊥ := fun h => by
    obtain ⟨m⟩ := hNE
    have := hsingle m
    rw [h, Submodule.mem_bot] at this
    exact hsne m this
  have hF3 : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) L0 ≤ -Real.log c0 :=
    max_slope_orthogonal_neg_log (monH K lam L0) (monH_frameOK K lam L0) (fun m : MonI lam => (Pi.single m 1 : MonI lam → K)) hsne
      (fun m m' h v => monH_orth K lam v m m' h) c0 hc0 (fun m v => by
        have := monH_norm_single K lam v m
        exact (hc m).trans (le_of_eq this.symm))
  obtain ⟨hBfg, -, hBmax, -⟩ := Formalism.LFunctionChainParameters.LLcv.ideal_scaling_holds K (MonI lam → K) (MonI lam) (Pi.basisFun K (MonI lam))
    (fun _ => (monD lam)⁻¹) hX' I hI0 L0 hL0fg hL00
  have hle : (delK lam M).map ((cfMap lam g).restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0 := by
    rintro _ ⟨x, hx, rfl⟩
    have e : (cfMap lam g).restrictScalars (𝓞 K) x = ∑ m, cfMap lam g x m • (Pi.single m 1 : MonI lam → K) := by
      funext m'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [e]
    refine sum_mem fun m _ => Submodule.subset_span ⟨_, ?_, _, hsingle m, rfl⟩
    rw [hI]
    exact coefficient_map_mem_twisted lam M g hg x hx m
  have hmap0 : (delK lam M).map ((cfMap lam g).restrictScalars (𝓞 K)) ≠ ⊥ := fun h => by
    have : (cfMap lam g).restrictScalars (𝓞 K) x0 ∈ (delK lam M).map ((cfMap lam g).restrictScalars (𝓞 K)) := ⟨x0, hx0, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hφx0 this
  have hSI := ((slope_inequality_mean K (VV K lam) (VVIdx lam) (MonI lam → K) (MonI lam) (tenH K lam M).b (tenH K lam M).X
    (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) hX hX' (cfMap lam g) (delK lam M) hΔ.fg hmap0).2
      (idealSmul (I : Submodule (𝓞 K) K) L0) hBfg hle).2 hinj.injOn
  have hH := coefficient_map_height_bound K lam hS g M hne hpos
  show muMaxDef (tenH K lam M).b (tenH K lam M).X (delK lam M) ≤ _
  rw [hBmax] at hSI
  linarith

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (coeff m P)‖ ^ 2 = ((coeff m P : ℚ) : ℝ) * ((coeff m P : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

theorem fock_norm_extremal_bound (hC : HwNormBound) {κ : ℕ} (lam : DomWeight (κ + 1)) :
    fockN (extremal ℂ (κ + 1) lam) ≤
      (∏ i, ((lam.natW i).factorial : ℝ)) * ((lam.natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := by
  rw [← Formalism.L2.DIV.map_extremal (algebraMap ℚ ℂ) (κ + 1) lam, fock_norm_rational_eq]
  have h := hC κ lam.natW (natural_weight_antitone lam)
  have h' : ((Formalism.GradedWeylDivisibility.fockQ (extremal ℚ (κ + 1) lam) (extremal ℚ (κ + 1) lam) : ℚ) : ℝ) ≤
      (((((∏ i, (lam.natW i).factorial : ℕ) : ℚ) * ((lam.natW 0 + κ + 1 : ℕ) : ℚ) ^ ((κ + 1) * κ / 2) : ℚ)) : ℝ) := by
    exact_mod_cast h
  refine h'.trans (le_of_eq ?_)
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem multi_factorial_eq_triple_prod (m : (ι × Fin n × Fin n) →₀ ℕ) : mfact m = ∏ τ : ι, ∏ s : Fin n, ∏ a : Fin n, (m (τ, a, s)).factorial := by
  unfold mfact
  rw [Finset.prod_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    rw [Finsupp.notMem_support_iff.1 hk, Nat.factorial_zero]), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fintype.prod_prod_type, Finset.prod_comm]

theorem factorial_prod_le_monomial (lam : ι → DomWeight n) (m : MonI lam) :
    ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ n ^ (∑ τ, dW (lam τ)) * mfact m.1 := by
  rw [multi_factorial_eq_triple_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun τ _ => ?_
  unfold dW
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← m.2 τ s]
  exact factorial_sum_le_pow_mul_prod fun a => m.1 (τ, a, s)

def monC {κ : ℕ} (lam : ι → DomWeight (κ + 1)) : ℝ :=
  (((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2))⁻¹

theorem monC_pos {κ : ℕ} (lam : ι → DomWeight (κ + 1)) : 0 < monC lam := by
  unfold monC
  have : ∀ τ, (0 : ℝ) < (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := fun τ => by positivity
  have h2 := Finset.prod_pos fun τ (_ : τ ∈ Finset.univ) => this τ
  positivity

theorem monomial_weight_lower_bound (hC : HwNormBound) {κ : ℕ} (lam : ι → DomWeight (κ + 1)) (m : MonI lam) : monC lam ≤ monW lam m := by
  unfold monC monW
  have hE : extremalFockNormProduct lam ≤ (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := by
    unfold extremalFockNormProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun τ _ => fockN_nonneg _) fun τ _ => fock_norm_extremal_bound hC (lam τ)
  have hM : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤ ((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * (mfact m.1 : ℝ) := by
    exact_mod_cast factorial_prod_le_monomial lam m
  have hP : 0 < ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) :=
    Finset.prod_pos fun τ _ => by positivity
  have hk : (0 : ℝ) < ((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos hk hP) (extR_pos lam), one_mul]
  calc extremalFockNormProduct lam ≤ (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) := hE
    _ ≤ (((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) * (mfact m.1 : ℝ)) * ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) :=
        mul_le_mul_of_nonneg_right hM hP.le
    _ = _ := by ring

theorem neg_log_monomial_constant {κ : ℕ} (lam : ι → DomWeight (κ + 1)) :
    -Real.log (monC lam) = ∑ τ, ((dW (lam τ) : ℝ) * Real.log ((κ : ℝ) + 1)
      + ((κ : ℝ) + 1) * (κ : ℝ) / 2 * Real.log (((lam τ).natW 0 : ℝ) + κ + 1)) := by
  unfold monC
  have hP : 0 < ∏ τ, (((lam τ).natW 0 : ℝ) + κ + 1) ^ ((κ + 1) * κ / 2) :=
    Finset.prod_pos fun τ _ => by positivity
  have hk : (0 : ℝ) < ((κ : ℝ) + 1) ^ (∑ τ, dW (lam τ)) := by positivity
  rw [Real.log_inv, neg_neg, Real.log_mul hk.ne' hP.ne', Real.log_pow, Real.log_prod (fun τ _ => by positivity),
    Finset.sum_add_distrib, Nat.cast_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_pow, triangular_number_cast]

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι]

theorem degree_weight_cast_eq {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : (dW lam : ℝ) = (wt (plus (castW h lam)) : ℝ) := by
  subst h
  unfold dW wt
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact_mod_cast natural_weight_cast_eq lam i

theorem det_shift_eq_last_weight {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : lam.detShift = castW h lam (Fin.last κ) := by
  subst h
  unfold DomWeight.detShift
  rw [dif_pos (Nat.succ_pos κ)]
  rfl

theorem max_slope_twisted_general (hS : FockSubNorm) (hC : HwNormBound) {n κ : ℕ} (h : κ + 1 = n) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) (g : ι → GL (Fin n) K)
    (hg : ∀ τ, ∀ x ∈ M τ, ∀ a, ((g τ : Matrix (Fin n) (Fin n) K) *ᵥ x) a ∈ (1 : Submodule (𝓞 K) K))
    (hpos : ∀ v τ, 0 < gN K g v τ)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0) (hI : (I : Submodule (𝓞 K) K) = twId lam M) :
    (tenH K lam M).muMax ≤
      ∑ τ, ((wt (plus (castW h (lam τ))) : ℝ) * (Real.log ((κ : ℝ) + 1) + (1 / (nPl K : ℝ)) * ∑ v, Real.log (gN K g v τ))
        + ((κ : ℝ) + 1) * (κ : ℝ) / 2 * Real.log ((plus (castW h (lam τ)) 0 : ℝ) + (κ : ℝ) + 1))
      - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  subst h
  have h1 := max_slope_twisted_lattice K lam hS M hM g hg hpos I hI0 hI (monC lam) (monC_pos lam) (monomial_weight_lower_bound hC lam)
  rw [neg_log_monomial_constant] at h1
  refine h1.trans (le_of_eq ?_)
  have e : ∀ τ, (((lam τ).natW 0 : ℕ) : ℝ) = (plus (castW rfl (lam τ)) 0 : ℝ) := fun τ => by
    exact_mod_cast natural_weight_cast_eq (lam τ) 0
  simp only [e, degree_weight_cast_eq rfl]
  rw [sub_add_eq_add_sub, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by ring

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQSplit
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

theorem qsp_exists_pi (P : Pl E) (hP : conjPrime₂ P ≠ P) : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal := by
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem (Ne.symm hP)
  exact ⟨s, hs, fun h => hns ((mem_conjP P s).2 h)⟩

include hc in

theorem qsp_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem qsp_isOver (P : Pl E) : IsOver (underPl F P) P := rfl

include hc in

theorem qsp_exists (P : Pl E) (hP : conjPrime₂ P ≠ P) :
    ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal ∧ Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E)) := by
  obtain ⟨ϖ, hϖ, hcϖ⟩ := qsp_exists_pi P hP
  obtain ⟨t, ht⟩ := gls_trace_mem hc ϖ
  obtain ⟨N, hN⟩ := qsp_norm_mem hc ϖ
  have hsig : ∀ x : E, hc.sig x = star x := fun _ => rfl
  have hsig0 : hc.sig (ϖ : E) = ((cO E ϖ : 𝓞 E) : E) := by rw [hsig]; exact (algebraMap_cO ϖ).symm
  have hN' : algebraMap F E (N : F) = (ϖ : E) * hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hN
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have ht' : algebraMap F E (t : F) = (ϖ : E) + hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_add, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have hNv : N ∈ (underPl F P).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    rw [hN]; exact Ideal.mul_mem_right _ _ hϖ
  have htv : t ∉ (underPl F P).asIdeal := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 E) t ∈ P.asIdeal := h
    rw [ht] at h1
    exact hcϖ (by simpa using P.asIdeal.sub_mem h1 hϖ)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 (underPl F P) ϖ t N ht' hN' hNv htv
  have hN2 : ((cO E ϖ : 𝓞 E) : E) * hc.sig ((cO E ϖ : 𝓞 E) : E) = algebraMap F E (N : F) := by
    rw [hN', ← hsig0, mul_comm, hsig, hsig, star_star]
  obtain ⟨sa⟩ := Formalism.MainNotions.Gaps.LG.sc_orient s (cO E ϖ) N hNv hN2
  have e : hc.sig ((cO E ϖ : 𝓞 E) : E) = (ϖ : E) := by rw [← hsig0, hsig, hsig, star_star]
  exact ⟨ϖ, hϖ, hcϖ, ⟨e ▸ sa⟩⟩

end Split

end Formalism.L2.Col
end
end

