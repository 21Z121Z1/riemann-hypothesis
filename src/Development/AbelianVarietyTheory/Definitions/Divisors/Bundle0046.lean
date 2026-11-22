import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

def IsQCart [IsLocallyNoetherian X] (D : X → ℚ) : Prop :=
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m

def QNum [IsLocallyNoetherian X] (p : X ⟶ Sp k) (N : LB X) (b : ℚ) (D : X → ℚ) : Prop :=
  letI := algebraΓOfHom p
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m ∧
    ∀ C : Closeds X, IsCompleteCurve k C →
      (interNumRed k C ![toLB D₀] : ℚ) / m = b * interNumRed k C ![N]

omit [IsIntegral X] in

def Off (B : X → ℚ) (z : X) : Prop := ∀ w, w ⤳ z → B w = 0

def CentreAt {p : X ⟶ Sp k} (E : DivOver p) (z : X) : Prop :=
  E.Through z ∧ ∀ f : X.functionFieldˣ, RegAt z (f : X.functionField) → E.ord f = 0 →
    RegAt z ((f⁻¹ : X.functionFieldˣ) : X.functionField)

def IsNkltCentre (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (z : X) : Prop :=
  ∃ (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ),
    η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Γ η z m g ∧ CentreAt E z ∧ discrep E η m g ≤ -1

def LcCut (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (x : X) (j : ℕ) : Prop :=
  LcAt p n Γ x ∧ ¬ KltAt p n Γ x ∧
    ∀ z, z ⤳ x → ¬ KltAt p n Γ z → topologicalKrullDim (closure ({z} : Set X)) ≤ j

theorem QNum.isQCart [IsLocallyNoetherian X] {p : X ⟶ Sp k} {N : LB X} {b : ℚ} {D : X → ℚ}
    (h : QNum p N b D) : IsQCart D := by
  obtain ⟨m, D₀, hm, he, hD, -⟩ := h
  exact ⟨m, D₀, hm, he, hD⟩

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
section
set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.GoodTop

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

abbrev EndValuedForm11Coeffs (n : ℕ) (r : Type) : Type := Fin n → Fin n → Matrix r r ℂ

def mixTop (K : Fin n → EndValuedForm11Coeffs n r) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
      (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det

def intersection_update_fsHerm_neg_one {α : Type} (K₁ L K₀ : α) (j : Fin n) : Fin n → α :=
  fun i => if i < j then K₁ else if i = j then L else K₀

def curvAt (G : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => curv G v (coordVec a) (coordVec b)

def cutForm (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => dbar (fun x => (ρ x : ℂ)) v (coordVec b) • (conn G₁ v (coordVec a) - conn G₀ v (coordVec a))

def corrC (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℂ :=
  ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)

def corrTop (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℝ := (Real.pi ^ n)⁻¹ * (corrC ρ G₀ G₁ v).re

def offHyp (S : Finset (Fin n)) (U : Set (V n)) : Set (V n) := {v | v ∈ U ∧ ∀ a ∈ S, v a ≠ 0}

section Glue

variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {κ : Type}

def HasInt (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) (t : ℝ) : Prop :=
  (∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S ≠ ⊤) ∧
    (glueMeas e fun i y => ENNReal.ofReal (((1 : ℤˣ) : ℤ) * d i y)).real S -
      (glueMeas e fun i y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * d i y)).real S = t

structure IsTopForm (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) : Prop where
  trans : ∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → d i y = ‖transDet (e i) (e j) y‖ ^ 2 * d j y
  meas : ∀ i, AEMeasurable (fun v => d i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))

end Glue

section Var

open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : ℕ}

def topDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  chernTop (MvPolynomial.X ((), X.dim)) (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)

def corrDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H₀ H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (ρ : CxPts X.str σ → ℝ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  corrTop (fun v => ρ (c.e.symm v)) (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)

structure GoodPatch (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) (S : Finset (Fin X.dim)) (A : Mat (fun _ : Unit => m) X.Fn)
    (W : Set (CxPts X.str σ)) (c : ℝ) : Prop where
  holo : IsHoloChart e
  isOpen : IsOpen W
  sub : W ⊆ e.source
  frame : ∀ z ∈ W, A ∈ E.S (under z)
  small : ∀ z ∈ W, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2
  mem : ∀ z ∈ W, z ∈ ptsIn X.str σ O ↔ ∀ a ∈ S, e z a ≠ 0
  form : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a i j,
    ‖conn (fun v => H A (e.symm v) ()) (e z) (coordVec a) i j‖ * poinWt S (e z) a ≤ c
  dbar : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a b i j,
    ‖curv (fun v => H A (e.symm v) ()) (e z) (coordVec a) (coordVec b) i j‖ * (poinWt S (e z) a * poinWt S (e z) b) ≤ c

theorem hasChernIntegral_iff (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (t : ℝ) :
    HasChernIntegral E O H (MvPolynomial.X ((), X.dim)) t ↔
      HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) t := Iff.rfl

end Var

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.FunObjModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem isMeasLevW_unique {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {good} {μ μ' : Measure (GA D V)}
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) (h : Lev.IsMeasLevW V K good μ) (h' : Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨hloc, hsc, ht2, hbor, htg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hall⟩ := h
  obtain ⟨hμ', -, hall'⟩ := h'
  obtain ⟨⟨A, hA⟩, hallA⟩ := hall θ hθ
  obtain ⟨⟨m, hm⟩, hallm⟩ := hallA A hA
  have hvol := hallm m hm
  have hvol' := (hall' θ hθ).2 A hA |>.2 m hm

  choose C hC hC1 using fun ρ => exists_compact_mem_nhds (1 : Formalism.BasicNotions.UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
  have hB : ∀ ρ, MeasurableSet (interior (C ρ)) := fun ρ => isOpen_interior.measurableSet
  have hpos : ∀ ρ, m ρ (interior (C ρ)) ≠ 0 := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact isOpen_interior.measure_ne_zero (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 (hC1 ρ)⟩
  have hfin : ∀ ρ, m ρ (interior (C ρ)) ≠ ⊤ := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact ((measure_mono interior_subset).trans_lt (hC ρ).measure_lt_top).ne
  have e1 := hvol (fun ρ => interior (C ρ)) hB
  have e2 := hvol' (fun ρ => interior (C ρ)) hB
  set P := ∏ ρ, m ρ (interior (C ρ)) with hPdef
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hpos ρ
  have hPtop : P ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hfin ρ
  have := hμ
  have := hμ'

  obtain ⟨c, hs⟩ : ∃ c : NNReal, μ' = c • μ := ⟨_, MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ' μ⟩
  have e3 : ∀ s, μ' s = c * μ s := fun s => by
    simp only [hs, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [e3, e1] at e2
  have hc1 : c = 1 := by exact_mod_cast (ENNReal.mul_eq_right hP0 hPtop).1 e2
  rw [hs, hc1, one_smul]

theorem isAt_unique {M M' : Vol G} {X : Node} {K} (h : M.IsAt X K) (h' : M'.IsAt X K) : M.ν X = M'.ν X := by
  unfold Vol.IsAt at h h'
  split_ifs at h h'
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1

variable (W : G.Weil)

theorem liftA_indep {M M' : Vol G} (a : Arrow T) {K} (h : M.IsAt a.src K) (h' : M'.IsAt a.src K) (f : Sch G a) (F : Fn G a.src)
    (hinv : ∀ x, ∀ γ ∈ GQ (G.V a.src), ∀ g, W.kerA a f (γ * g) x * F (γ * g) = W.kerA a f g x * F g) :
    liftA W M a f F = liftA W M' a f F := by
  obtain ⟨hloc, hsc, ht2, hbor, htg, hdisc, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.src)
  have hν : M.ν a.src = M'.ν a.src := isAt_unique h h'
  obtain ⟨hH, hfd⟩ := h.haar_fund
  obtain ⟨-, hfd'⟩ := h'.haar_fund
  rw [← hν] at hfd'
  funext x
  rw [liftA_apply, liftA_apply, ← hν]
  exact hfd.setIntegral_eq hfd' fun γ y => hinv x γ γ.2 y

theorem embTop_hom : ∃ s : GA D (G.V (.top 0)) →* GA D (G.V (.grid D.R.m 0)), Continuous s ∧ embTop G = s ∧
    ∀ γ ∈ GQ (G.V (.top 0)), s γ ∈ GQ (G.V (.grid D.R.m 0)) := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨s, hc, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ (G.rowDec 0 hm).ι (G.rowDec 0 hm).isom
  refine ⟨s, hc, ?_, hrat⟩
  funext h
  exact ((embRel_iff _ h (s h)).mp ((hrel h (s h)).mpr rfl)).symm

private theorem besChar_mul_eq_of_embRel {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)
    (ψ : AddChar (AF D.host.F) ℂ) (g n : GA D B) (h : GA D A) (hrel : EmbRel B A ι g h) :
    besChar ψ d (n * g) = besChar ψ d n := by

  have key : ∀ x : Fin B.rank → D.host.E,
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).mulVec x = 0 →
      (subOne B (n * g)).mulVec (ratV x) = (subOne B n).mulVec (ratV x) := by
    intro x hx
    have h2 : ((matHom B g).1 : Matrix _ _ _).mulVec (ratV x) = ratV x := hrel.2 x hx
    rw [subOne, subOne, map_mul, Units.val_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, h2]
  have hcol : ∀ i, (subOne B (n * g)).mulVec (ratV fun k => d.e k i) = (subOne B n).mulVec (ratV fun k => d.e k i) := by
    intro i
    apply key
    funext j
    have := congrFun (congrFun d.e_perp j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hz := key d.z d.z_perpA
  have hP : IsBesVal ψ d (n * g) = IsBesVal ψ d n := by
    funext v
    simp only [IsBesVal, hcol, hz]
  unfold besChar
  rw [hP]

theorem exists_Bplus_ne_zero {M : Vol G} (hM : M.IsRow) : ∃ φ F, BplusConv W M φ F ∧ Bplus W M φ F ≠ 0 := by
  have hψ0 : ∀ x, W.ψ x ≠ 0 := fun x h0 => by
    have := W.ψ.map_add_eq_mul x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have hchi0 : ∀ g, besChar W.ψ G.besTop g ≠ 0 := by
    intro g
    unfold besChar
    split_ifs with hv
    · obtain ⟨a, b, -, -, hval⟩ := hv.choose_spec
      rw [hval]
      exact hψ0 _
    · exact one_ne_zero
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega

  have hfun : besInt W (fun _ => (1 : ℂ)) (fun g => (star (besChar W.ψ G.besTop g))⁻¹) = fun _ _ => 1 := by
    funext h n
    have hrel : EmbRel _ _ (G.rowDec 0 hm).ι (embTop G h) h := (embRel_iff (G.rowDec 0 hm) h (embTop G h)).mpr rfl
    simp only [besInt, one_mul]
    rw [besChar_mul_eq_of_embRel G.besTop W.ψ (embTop G h) (n : GA D _) h hrel]
    exact inv_mul_cancel₀ (star_ne_zero.2 (hchi0 _))
  obtain ⟨-, -, hN⟩ := hM.unip
  have hq := GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D _ (M.ν (.top 0)) (M.fd (.top 0)) hM.top.haar_fund
  refine ⟨fun _ => 1, fun g => (star (besChar W.ψ G.besTop g))⁻¹, ?_, ?_⟩
  · unfold BplusConv
    rw [hfun]
    refine ⟨fun h => integrableOn_const (by rw [hN]; simp), ?_⟩
    simp only [setIntegral_const, Measure.real, hN]
    exact integrableOn_const hq.2
  · unfold Bplus
    rw [hfun]
    simp [Measure.real, hN]
    exact ENNReal.toReal_ne_zero.2 hq

theorem tensT_single {X Y : Node} {p : Path T X Y} (P : PolT G p) (d : PureT G p) (c c' : ℂ) :
    tensT W (Finsupp.single P c) (Finsupp.single d c') =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) (c * c') := by
  simp [tensT, Finsupp.sum_single_index]

theorem levJ_col (t : T) (j : ℕ) : levJ G t (.grid 0 (j + 1)) = levCol L t j := rfl

example (t : T) : (givenPath t 3).arrows = [.down t 0 2, .down t 0 1, .down t 0 0, .right 0 0, .right 1 0, .right 2 0] ∧
    (oppPath t 3).arrows = [.right 0 3, .right 1 3, .right 2 3, .down t 3 2, .down t 3 1, .down t 3 0] := ⟨rfl, rfl⟩

example (M : Vol G) (t : T) (f : ∀ j : Fin 2, Sch G (.down t 0 j)) (u : Fn G (.grid 0 2)) :
    liftP W M (downPath t 0 2) (downFam t 0 2 f) u = liftA W M (.down t 0 0) (f 0) (liftA W M (.down t 0 1) (f 1) u) := rfl

end GlobalTheory.FunObjModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDataOfPositivity
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem exists_intGens : ∃ (n : ℕ) (w : Fin n → Fin G.N → F),
    Submodule.span ℤ (Set.range w) = G.lattice.restrictScalars ℤ := by
  have h : G.lattice.FG := Submodule.fg_span (Set.finite_range _)
  have : Module.Finite (𝓞 F) G.lattice := Module.Finite.iff_fg.2 h
  have : Module.Finite ℤ G.lattice := Module.Finite.trans (𝓞 F) _
  have h' : (G.lattice.restrictScalars ℤ).FG := Module.Finite.iff_fg.1 this
  exact Submodule.fg_iff_exists_fin_generating_family.1 h'

def regen {n : ℕ} (w : Fin n → Fin G.N → F) (hw : Submodule.span F (Set.range w) = ⊤) (Λ : ℝ) : Geo F :=
  { G with
    n := n
    w := Matrix.of fun j k => w k j
    abelian₂ := Λ
    geom := ⟨⟨G.geom.alg.variety, G.geom.alg.indep, hw, G.geom.alg.bpf⟩, G.geom.bd_ne⟩
    herm := G.herm
    conj := G.conj
    alg₂ := ⟨G.alg₂.1, G.alg₂.2, G.alg₂.3, G.alg₂.4⟩
    herm₂ := G.herm₂
    conj₂ := G.conj₂
    U_le := G.U_le }

theorem exists_regen : ∃ (n : ℕ) (w : Fin n → Fin G.N → F) (hw : _) (Λ : ℝ),
    (regen G w hw Λ).ShortGenerators ∧ (regen G w hw Λ).lattice = G.lattice := by
  obtain ⟨n, w, h⟩ := exists_intGens G
  have hm (k) : w k ∈ G.lattice := h.le (Submodule.subset_span ⟨k, rfl⟩)
  have hl : Submodule.span (𝓞 F) (Set.range w) = G.lattice :=
    le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hm))
      fun u hu => Submodule.span_le_restrictScalars ℤ (𝓞 F) _ (h.ge hu)
  have hw : Submodule.span F (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 F), hl, HermSys.lattice, Submodule.span_span_of_tower]
    exact G.geom.alg.spans
  refine ⟨n, w, hw, 1 + ∑ k, ∑ σ : F →+* ℂ, G.normAt σ (w k), ⟨fun u hu => h.ge (hl.le hu), fun k σ => ?_, ?_⟩, hl⟩
  · have h0 (k) (σ : F →+* ℂ) : 0 ≤ G.normAt σ (w k) := Real.sqrt_nonneg _
    exact ((Finset.single_le_sum (fun σ _ => h0 k σ) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun k => ∑ σ : F →+* ℂ, G.normAt σ (w k))
        (fun k _ => Finset.sum_nonneg fun σ _ => h0 k σ) (Finset.mem_univ k))).trans (le_add_of_nonneg_left zero_le_one)
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)

theorem positivity_regen (h : G.Positivity) {n : ℕ} (w : Fin n → Fin G.N → F) (hw) (Λ : ℝ) :
    (regen G w hw Λ).Positivity :=
  ⟨⟨h.bir.1, h.bir.2, h.bir.3, h.bir.4, h.bir.5⟩, h.nef, h.big⟩

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

def mulG (j : ℕ) : (Fin G.N → F) →ₗ[F] G.global j →ₗ[F] G.global (j + 1) :=
  LinearMap.mk₂ F (fun u f => ⟨G.mulW j u f, mulW_mem_global G j u f.2⟩)
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))

def lat (j : ℕ) : Submodule (𝓞 F) (G.global j) :=
  Nat.rec (motive := fun j => Submodule (𝓞 F) (G.global j))
    (Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global 0))))
    (fun j M => Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global (j + 1)))) ⊔
      Submodule.map₂ ((mulG G j).restrictScalars₁₂ (𝓞 F) (𝓞 F)) G.lattice M) j

theorem basis_mem_lat (j : ℕ) (i) : Module.finBasis F (G.global j) i ∈ lat G j := by
  cases j with
  | zero => exact Submodule.subset_span ⟨i, rfl⟩
  | succ j => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem isFull_lat (j : ℕ) : IsFull (lat G j) := by
  refine ⟨?_, top_le_iff.1 ((Module.finBasis F (G.global j)).span_eq.ge.trans
    (Submodule.span_mono (Set.range_subset_iff.2 (basis_mem_lat G j))))⟩
  induction j with
  | zero => exact Submodule.fg_span (Set.finite_range _)
  | succ j ih =>
    have h : G.lattice.FG := Submodule.fg_span (Set.finite_range _)
    exact (Submodule.fg_span (Set.finite_range _)).sup (h.map₂ _ ih)

def data (T : ℕ) (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β) : Data F :=
  { G.globalData T hT with M := lat G, full := isFull_lat G, beta := β, one_le_beta := hβ, J := J }

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)

theorem mulStable : (data G T hT β J hβ).MulStable := fun j _ w hw f hf =>
  have h : mulG G j w f ∈ lat G (j + 1) := Submodule.mem_sup_right
    (Submodule.apply_mem_map₂ ((mulG G j).restrictScalars₁₂ (𝓞 F) (𝓞 F)) hw hf)
  ⟨mulG G j w f, h, rfl⟩

theorem shortFamily (j : ℕ) : (data G T hT β J hβ).ShortFamily j 1 :=
  have e := (data G T hT β J hβ).latRank_M j
  ⟨Module.finBasis F (G.global j) ∘ Fin.cast e, fun _ => basis_mem_lat G j _,
    (Module.finBasis F (G.global j)).linearIndependent.comp _ (Fin.cast_injective e),
    fun _ σ => (nrm_ofBasis _ σ _).le⟩

omit [NumberField F] in

theorem nrm_ofBasis_eq {V n : Type} [AddCommGroup V] [Module F V] [Fintype n] [DecidableEq n]
    (b : Module.Basis n F V) (σ : F →+* ℂ) (x : V) :
    (ofBasis b).nrm σ x = Real.sqrt (∑ i, ‖σ (b.repr x i)‖ ^ 2) := by
  simp [HermFam.nrm, ofBasis, ofGram, ofCoords, basisCoords, dotProduct, Complex.conj_mul', ← Complex.ofReal_pow]

theorem exists_bound {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] {N m m' : ℕ}
    (b : Module.Basis (Fin m) F V) (b' : Module.Basis (Fin m') F V') (μ : (Fin N → F) →ₗ[F] V →ₗ[F] V')
    (σ : F →+* ℂ) {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ w f, (ofBasis b').nrm σ (μ w f) ≤ c * frameNorm A (fun k => σ (w k)) * (ofBasis b).nrm σ f := by
  refine ⟨∑ l, ∑ k, ∑ i, archSize A (Pi.single k 1) * ‖σ (b'.repr (μ (Pi.single k 1) (b i)) l)‖,
    by unfold archSize; positivity, fun w f => ?_⟩
  have hw (k) : ‖σ (w k)‖ ≤ frameNorm A (fun k => σ (w k)) * archSize A (Pi.single k 1) := by
    simpa [Pi.single_apply] using norm_pairing_le hA (fun k => σ (w k)) (Pi.single k 1)
  have hf (i) : ‖σ (b.repr f i)‖ ≤ (ofBasis b).nrm σ f := by
    rw [nrm_ofBasis_eq]
    exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun i => ‖σ (b.repr f i)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  have e (l) : b'.repr (μ w f) l = ∑ k, ∑ i, w k * b.repr f i * b'.repr (μ (Pi.single k 1) (b i)) l := by
    conv_lhs => rw [pi_eq_sum_univ' w, ← b.sum_repr f]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [nrm_ofBasis_eq b']
  refine (Real.sqrt_le_iff.2 ⟨by positivity, Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _⟩).trans ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [e, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, map_mul, norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_right (mul_le_mul (hw k) (hf i) (norm_nonneg _) ((norm_nonneg _).trans (hw k)))
    (norm_nonneg (σ (b'.repr (μ (Pi.single k 1) (b i)) l)))
  linarith

theorem exists_mulBound : ∃ β₀ : ℝ, ∀ β ≥ β₀, ∀ (hβ : 1 ≤ β) (J : ℝ), (data G T hT β J hβ).MulBound fun _ => β := by
  choose c h0 hc using fun (j : ℕ) (σ : F →+* ℂ) => exists_bound (Module.finBasis F (G.global j))
    (Module.finBasis F (G.global (j + 1))) (mulG G j) σ (G.herm σ)
  refine ⟨(∑ j ∈ Finset.range T, ∑ σ, c j σ) ^ 2, fun β h _ J j hj σ w _ f _ g e => ?_⟩
  obtain rfl : g = mulG G j w f := Subtype.ext e
  have h₁ : c j σ ≤ Real.sqrt β := Real.le_sqrt_of_sq_le ((pow_le_pow_left₀ (h0 j σ)
    ((Finset.single_le_sum (fun σ _ => h0 j σ) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun j => ∑ σ, c j σ) (fun j _ => Finset.sum_nonneg fun σ _ => h0 j σ)
        (Finset.mem_range.2 hj))) 2).trans h)
  exact (hc j σ w f).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h₁ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

include hT in

theorem exists_data_of_positivity (h : G.Positivity) :
    ∃ X : Data F, X.D = G.D ∧ X.T = T ∧ X.d = Module.finrank F (G.global T) ∧ X.del = G.del ∧ X.Positivity ∧
      X.MulStable ∧ X.MulBound (fun _ => X.beta) ∧ X.ShortGenerators ∧ X.ShortFamily X.D X.LamD ∧
      X.ShortFamily X.T X.LamT := by
  obtain ⟨n, w, hw, Λ, hs, -⟩ := exists_regen G
  obtain ⟨β, hβ⟩ := exists_mulBound (regen G w hw Λ) (T := T) hT
  have h1 := le_max_right β 1
  exact ⟨data (regen G w hw Λ) T hT (max β 1) 0 h1, rfl, rfl, Data.d_eq_finrank _, rfl,
    positivity_regen G h w hw Λ, mulStable (regen G w hw Λ) hT _ 0 h1, hβ _ (le_max_left _ _) h1 0, hs,
    shortFamily (regen G w hw Λ) hT _ 0 h1 _, shortFamily (regen G w hw Λ) hT _ 0 h1 _⟩

omit G in

theorem exists_data {M : ℕ} (hM : 1 ≤ M) {T : ℕ} (hT : M + 1 ≤ T) :
    ∃ X : Data F, X.D = M ∧ X.T = T ∧ 0 < X.d ∧ X.del = 1 ∧ X.Positivity ∧ X.MulStable ∧
      X.MulBound (fun _ => X.beta) ∧ X.ShortGenerators ∧ X.ShortFamily X.D X.LamD ∧ X.ShortFamily X.T X.LamT := by
  obtain ⟨X, h₁, h₂, h₃, h₄, h⟩ := exists_data_of_positivity (Proj.geo F hM) (T := T) hT (Proj.positivity F hM)
  exact ⟨X, h₁, h₂, (Proj.finrank_global_pos F hM T).trans_eq h₃.symm, h₄.trans (projSys.del_eq_one F M), h⟩

omit G in

theorem not_shortGenerators_geo [IsTotallyComplex F] {M : ℕ} (hM : 1 ≤ M) : ¬ (Proj.geo F hM).ShortGenerators := by
  intro h
  have key (a : 𝓞 F) : ∃ z : ℤ, (a : F) = z := by
    have hm : a • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) F).col 0 ∈ (Proj.geo F hM).lattice :=
      (Proj.geo F hM).lattice.smul_mem a (Submodule.subset_span ⟨(0 : Fin (M + 1)), rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (h.int _ hm)
    have : (∑ i : Fin (M + 1), c i • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) F).col i) 0 =
      (a • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) F).col 0) 0 := congrFun hc (0 : Fin (M + 1))
    exact ⟨c (0 : Fin (M + 1)), by simpa [Matrix.one_apply, Algebra.smul_def] using this.symm⟩
  obtain ⟨σ⟩ : Nonempty (F →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  obtain ⟨p, hp⟩ := key a
  obtain ⟨q, hq⟩ := key b
  rw [show algebraMap (𝓞 F) F a = p from hp, show algebraMap (𝓞 F) F b = q from hq]
  simp

end GlobalTheory.HilbertSamuel.Model
end
end

