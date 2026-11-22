import Mathlib
import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.Bundle0014
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0030
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FinalW
import Formalism.LocalToGlobal.Columns.Bundle0009
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.Columns.AtTOwedV
import Formalism.LocalToGlobal.Columns.Bundle0007
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.GL3MeanSquares.Bundle0002
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.Bundle0013
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalToGlobal.Columns.TiedCG
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

-- bundled from Formalism.LocalToGlobal.Columns.BrzColLatOneLattice
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
  (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)

theorem isSesq_formAt : IsSesq (formAt b P) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [formAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · simp only [formAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem gramOf_formAt [DecidableEq ι] (v : InfinitePlace K) :
    gramOf b (formAt b P v) = Matrix.of fun i j => v.embedding (P (b i) (b j)) := by
  ext i j
  simp only [gramOf, Matrix.of_apply, formAt, Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i' _ hi
    simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem posAt_formAt [DecidableEq ι] (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef) :
    PosAt b (formAt b P) := fun v => by rw [gramOf_formAt]; exact hpos v

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [DecidableEq ι]

theorem formH_spec (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef)
    (L : Submodule (𝓞 K) V) :
    FrameOK (ofFormB b L (formAt b P)) ∧
    (∀ v (x y : V), Formalism.HermitianLatticesTheory.majAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x y = formAt b P v x y) ∧
    (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x =
      Real.sqrt (formAt b P v x x).re) :=
  of_form_spec K V ι b L (formAt b P) (isSesq_formAt b P) (posAt_formAt b P hpos)

theorem formH_good (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : (ofFormB b L (formAt b P)).Good :=
  ⟨(formH_spec b P hpos L).1, hL.fg, hL.span_eq_top⟩

end Forms

theorem hlat_mu_le_muMax {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K) (hX : FrameOK A) (hL : A.L.FG)
    (hne : A.L ≠ ⊥) : A.mu ≤ A.muMax := by
  have h1 := (Formalism.HN.plLat K A.V A.ι A.b A.X hX A.L hL).1
  have h2 := (Formalism.HN.muChar (𝓞 K) A.V _ (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L h1 hne).2.2.2.2
  unfold HLat.mu HLat.muMax Formalism.HN.muDef Formalism.HN.muMaxDef
  linarith

theorem isLattice_ne_bot {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Nontrivial V] {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : L ≠ ⊥ := by
  intro h
  have h2 := hL.span_eq_top
  rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at h2
  exact bot_ne_top h2

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem GSD.Rat.pos' (R : S.Rat) (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (S.pair (S.bV i) (S.bV j))).PosDef := R.pos v

theorem GSD.valH_spec (R : S.Rat) (d : S.D) :
    FrameOK (S.valH d) ∧
    (∀ v (x y : S.V), Formalism.HermitianLatticesTheory.majAt (S.valH d).b (S.valH d).X v x y = S.pairAt v x y) ∧
    (∀ v (x : S.V), Formalism.HermitianLatticesTheory.normAt (S.valH d).b (S.valH d).X v x = Real.sqrt (S.pairAt v x x).re) :=
  formH_spec S.bV S.pair R.pos' (S.Del d)

theorem GSD.valH_good (R : S.Rat) (d : S.D) (hD : Submodule.IsLattice K (S.Del d)) : (S.valH d).Good :=
  formH_good S.bV S.pair R.pos' hD

theorem GSD.valNabH_good (R : S.Rat) (d : S.D) (hD : Submodule.IsLattice K (S.Nab d)) : (S.valNabH d).Good :=
  formH_good S.bV S.pair R.pos' hD

end Val

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

theorem stdPair_pos (v : InfinitePlace K) :
    (Matrix.of fun i j => v.embedding (stdPair K lam (bVV K (oneW lam) i) (bVV K (oneW lam) j))).PosDef :=
  pairPos K Unit n (oneW lam) _ v.embedding fun _ => by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one

theorem stdNabL_eq : stdNabL K lam = nabK (oneW lam) fun _ => colLat (1 : GL (Fin n) K) := by
  unfold stdNabL nabK
  have h := (nabDelFree K Unit n (oneW lam) 1).1
  have h1 : (nabStd K (oneW lam)).map ((actP (oneW lam) (1 : Unit → GL (Fin n) K)).restrictScalars (𝓞 K)) = nabStd K (oneW lam) := by
    ext F
    simp [polyAction_one₂]
  rw [h1] at h
  rw [← h]
  rfl

theorem stdDelL_eq : stdDelL K lam = delK (oneW lam) fun _ => colLat (1 : GL (Fin n) K) := by
  unfold stdDelL delK
  have h := (nabDelFree K Unit n (oneW lam) 1).2
  have h1 : (delStd K (oneW lam)).map ((actP (oneW lam) (1 : Unit → GL (Fin n) K)).restrictScalars (𝓞 K)) = delStd K (oneW lam) := by
    ext F
    simp [polyAction_one₂]
  rw [h1] at h
  rw [← h]
  rfl

theorem brz_colLat_one_lattice : Submodule.IsLattice K (colLat (1 : GL (Fin n) K)) := by
  have e : colLat (1 : GL (Fin n) K) = stdLat K n := by
    ext x
    rw [lc_mem_colLat_one]
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact stdLat_lattice

theorem stdNabL_isLattice : Submodule.IsLattice K (stdNabL K lam) := by
  rw [stdNabL_eq]
  exact (nabDelLattice K Unit n (oneW lam) _ fun _ => brz_colLat_one_lattice K).1

theorem stdDelL_isLattice : Submodule.IsLattice K (stdDelL K lam) := by
  rw [stdDelL_eq]
  exact (nabDelLattice K Unit n (oneW lam) _ fun _ => brz_colLat_one_lattice K).2

theorem stdNabH_good : (stdNabH K lam).Good := formH_good _ _ (stdPair_pos K lam) (stdNabL_isLattice K lam)

theorem stdDelH_good : (stdDelH K lam).Good := formH_good _ _ (stdPair_pos K lam) (stdDelL_isLattice K lam)

theorem stdNabL_ne_bot : stdNabL K lam ≠ ⊥ := by
  exact isLattice_ne_bot (stdNabL_isLattice K lam)

theorem stdDelL_ne_bot : stdDelL K lam ≠ ⊥ := by
  exact isLattice_ne_bot (stdDelL_isLattice K lam)

theorem stdDelL_le : stdDelL K lam ≤ stdNabL K lam :=
  Submodule.comap_mono (delStd_le_nabStd K (oneW lam))

theorem slopeLeMax : SlopeLeMax K lam :=
  hlat_mu_le_muMax (stdNabH K lam) (stdNabH_good K lam).1 (stdNabH_good K lam).2.1 (stdNabL_ne_bot K lam)

end Std

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem colValH_good (hX : X.Ok) (u : Pr.Word) (j : ℕ) (d : (colGSD W Ch u j).D) : ((colGSD W Ch u j).valH d).Good :=
  GSD.valH_good (colRat W Ch hX u j) d (thl_colDel_isLattice W Ch u j d)

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.InputsGenus
section
noncomputable section

namespace Formalism.L2.Col

open NumberField

theorem unimodGenusLocAll_holds : UnimodGenusLocAll := unimodular_genus_unique

theorem unimodGenusLoc_holds (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : UnimodGenusLoc E n :=
  unimodGenusLocAll_holds E n

theorem unimodGenus_holds {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] : UnimodGenus hc n :=
  (Formalism.L2.GenusGluing.Gen.unimodGenus_iff hc n).1 (unimodGenusLoc_holds E n)

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RamifiedOperatorsNonvacuous
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

end Gen

section LemC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end LemC

section Det

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Det

section T5

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable [Nonempty X.Tau]

end T5

section Nab

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Nab

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

theorem list_prod_intertwines {K : Type} [Field K] {V V' ι : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (k : V →ₗ[K] V') (A : ι → Module.End K V) (A' : ι → Module.End K V') (c : ι → K)
    (h : ∀ i, (A' i).comp k = c i • k.comp (A i)) (l : List ι) :
    ((l.map A').prod).comp k = (l.map c).prod • k.comp (l.map A).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    have e1 : (A' i * (l.map A').prod).comp k = (A' i).comp (((l.map A').prod).comp k) := rfl
    rw [e1, ih, LinearMap.comp_smul, ← LinearMap.comp_assoc, h i, LinearMap.smul_comp, smul_smul, mul_comm (l.map c).prod]
    rfl

theorem KernelArgumentHypothesisScalar.prod {u : Pr.Word} {kk : KerArg W Ch u} {c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ} (h : KernelArgumentHypothesisScalar kk c) (w : HeightOneSpectrum (𝓞 X.K))
    (j : ℕ) (hj : j < R.m) :
    (UprodC W Ch u (j + 1) w).comp (kk j) = ((cProdC W c w j : X.Kˣ) : X.K) • (kk j).comp (UprodC W Ch u j w) := by
  have := list_prod_intertwines (kk j) (fun P => UOp W Ch u j P) (fun P => UOp W Ch u (j + 1) P) (fun P => ((c j P : X.Kˣ) : X.K))
    (fun P => h j hj P) (VVTc W u w).toList
  unfold UprodC cProdC
  rw [this, Units.coe_prod, Finset.prod_map_toList]

end Col

section NonDeg

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem VVTc_nonempty (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (hw : seenC Pr u w) (ht : W.tops.Nonempty) :
    (VVTc W u w).Nonempty := by
  obtain ⟨τ, hτ⟩ := ht
  exact ⟨⟨pullW τ w, (seenC_iff hPr u w).1 hw τ⟩, (mem_VVTc W u w _).2 ⟨τ, by rw [topsP_of_seenC W hPr u w hw]; exact hτ, rfl⟩⟩

end NonDeg

section AutomorphicFormsHyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AutomorphicFormsHyp

section Price

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Price

section Vals

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end Vals

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end GSD

section ValsCol

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ValsCol

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecLevelStep
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG : Finset (Pl E)} (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))
  {π : 𝓞 E} {T f : ℕ}

def stepOf (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG)
    (hidx : (baseLb E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f))
    (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ) :
    Formalism.L2.Forms.StepLevel F E hc.sig (1 : Matrix (Fin n) (Fin n) E) T f (plUnder F SG) where
  Lb := baseLb E n ST
  Lb_fin := baseLb_fin n ST
  Lb_span := baseLb_span n ST
  Lb_int := baseLb_int hc n ST
  Lb_dual := baseLb_dual hc n ST (fun P hP => (hST P).1 hP) hTπ
  Lb_index := hidx
  Uloc := levLoc hc n ST SG (Subgroup.pi Set.univ Hw)
  Uloc_le := levLoc_le hc n ST SG _
  Uloc_lev := levLoc_le_levelVL hc n ST SG _
  Uloc_hyp v hv hT := levLoc_eq_levelVL hc n ST SG _ v
    (fun h => hT ((mem_plUnder_iff_norm hc hST T hTπ v).1 h)) hv
  fM v _ := fMod hc n ST v
  fT v _ := fLoc hc n ST v
  fT_ne v h := fLoc_ne hc n v hB ((mem_plUnder_iff_norm hc hST T hTπ v).2 h)
  fT_T v _ x := fLoc_natCast_smul_eq_zero_of_dvd hc n v hB T ⟨cO E π, hTπ.symm⟩ x
  fM_card v h := by
    obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    rw [fMod_card hc n v hB hP hov (hB.over_unique hc hP hov), hcard P hP]
  fT_L v _ x hx := fLoc_L hc n v x hx
  UlocAlt v h := levLoc_eq_stabFun hc n SG _ v hB (hSG v h)
  U := levU hc n ST SG (Subgroup.pi Set.univ Hw)
  U_eq x := levU_eq_prod hc n ST SG Hw x
  U_compact := levU_compact hc n ST SG _
  U_open := levU_open hc n ST SG _
  chi := levTyp lam
  chi_triv x h := levTyp_eq_one hc n ST SG _ lam x h

end Gen

section Col

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rls_T_notUnder (hPr : Pr.Ok) (u : Pr.Word) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal) :
    v ∉ plUnder X.F Pr.vGs := by
  rintro ⟨w, hw, hov⟩
  apply T_notMem_vGs hPr u ⟨w, hw⟩
  have : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ h
  rwa [Ideal.mem_comap, map_natCast] at this

theorem rls_vT_iff (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (P : Pl X.E) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal :=
  mem_divs (basePi_of_ok hX hPr u).ne_zero P

def colStep (hc : Formalism.BasicNotions.CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (j : ℕ) :
    Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs) :=
  stepOf hc (R.N j) (fun w => (colLev Ch j w).H) (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = Pr.T u)) (rls_T_notUnder hPr u)
    (colBase_index hc (R.N j) hPr u) ((Units.map σ₀.toMonoidHom).comp (colLev Ch j).chr)

theorem colStep_U (hc : Formalism.BasicNotions.CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m) (σ₀ : X.K →+* ℂ) (u : Pr.Word) (j : ℕ) :
    (colStep hc hX hPr Ch σ₀ u j).U = colU hc Ch u j := rfl

end Col

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCB
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

set_option maxHeartbeats 4000000 in

structure Joint {D : ColRec} (X : CH.ColsHerm D) (u : D.what₂.Word) (T : FormsTied D u) : Prop where

  eV : T.atT.eV = X.base.vT u
  piU : T.atT.piU = (X.atT u).piU
  res : T.atT.res = (X.atT u).res

  car0 : SameCar (rank_eq_first_level D.R) (X.base.lev0 u).Lb (T.cls 0 (Nat.zero_le _)).lev.Lb
    (X.base.lev0 u).Uloc (T.cls 0 (Nat.zero_le _)).lev.Uloc (X.base.lev0 u).U (T.cls 0 (Nat.zero_le _)).lev.U
    (fun c => ((X.base.lev0 u).y c).1) (fun c => ((T.cls 0 (Nat.zero_le _)).y c).1)
    (fun c s => ((X.base.lev0 u).stabI c s).1) (fun c s => ((T.cls 0 (Nat.zero_le _)).stabI c s).1)

  carI : ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m), SameCar (rankN D i hm) (X.base.lev u i h1 hm).Lb (T.cls i hm).lev.Lb
    (X.base.lev u i h1 hm).Uloc (T.cls i hm).lev.Uloc (X.base.lev u i h1 hm).U (T.cls i hm).lev.U
    (fun c => ((X.base.cls u i h1 hm).y c).1) (fun c => ((T.cls i hm).y c).1)
    (fun c s => ((X.base.cls u i h1 hm).stabI c s).1) (fun c s => ((T.cls i hm).stabI c s).1)

  carP : SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) T.clsP.lev.Lb
    (X.atT u).levP.Uloc T.clsP.lev.Uloc (X.atT u).levP.U T.clsP.lev.U
    (fun c => ((X.atT u).clsP.y c).1) (fun c => (T.clsP.y c).1)
    (fun c s => ((X.atT u).clsP.stabI c s).1) (fun c s => (T.clsP.stabI c s).1)
  lattice₂ : ∀ c, T.clsP.lat c = ((X.atT u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))

  pr : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : CH.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).pr v c z' = (X.atT u).pr i v c z
  prk : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : CH.Lk D u ((X.atT u).Pv v) i c) (z' : Lk T.atT i hi v c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).prk v c z' = (X.atT u).prk i v c z

  z0 : T.til.z0 = crdN D D.R.m le_rfl (X.atT u).z0
  ga : ∀ c, (T.til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((X.atT u).tilG c).1)

  sp : T.gl.sp = (X.base.lev0 u).splitG
  piG : T.gl.piG = (X.levelZeroCompatibility u).piG
  fr0 : ∀ i v h, (T.glev 0 (Nat.zero_le _)).fr i v h = reGL (rank_eq_first_level D.R) _ ((X.base.lev0 u).frG i v h)

structure ColsTied (D : ColRec) where
  herm : CH.ColsHerm D
  forms : ∀ u : D.what₂.Word, FormsTied D u
  joint : ∀ u, Joint herm u (forms u)
  gl_const : ∀ u u', (forms u).gl = (forms u').gl

  chi : CharacterCompatible (forms D.u₀).gl D.R.m

  fr_const : ∀ u u' (i : ℕ) (hi : i ≤ D.R.m), i < D.R.m → ((forms u).glev i hi).fr = ((forms u').glev i hi).fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

end Formalism.L2.Col.CF

end
end

