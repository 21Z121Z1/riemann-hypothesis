import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread)

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

open Classical in

def ExpBd (k : ℕ) (cx : Lt1 Dw → ℕ) (Mb Sm : ℝ) (M : ℕ) : Prop :=
  0 ≤ Mb ∧ (∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) ∧
    (sumSmallSpread k cx : ℝ) ≤ Sm ∧ ∀ f, cx f ≤ M

def Shape (F k m : ℕ) : Prop :=
  Dw.p + Dw.q + 1 = k + m ∧ Dw.q ≤ m ∧ m ≤ k ∧ 1 ≤ m ∧ 2 ≤ k ∧ Module.finrank ℚ E = 2 * F

def WtBd (k n : ℕ) (u : Weight Dw) (B : ℕ) (Sg : ℝ) : Prop :=
  (∀ τ, Antitone (u τ)) ∧ (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) ∧
    (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) ∧
    (∀ τ i, |u τ i| ≤ B) ∧
    ∀ τ, (∑ i ∈ Finset.univ.filter (fun i : Fin (Dw.p + Dw.q) => (i : ℕ) + 2 < k), (u τ i : ℝ)) ≤ Sg

end Free

def eSmall (F N m : ℕ) (Mb Sm : ℝ) (M p : ℕ) : ℝ :=
  (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) + F * (m + 1) * (N : ℝ) ^ 2 * (Real.logb p M + 1)

open Classical in

def eOf (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (M : ℕ) (S R : Finset ℕ) (p : ℕ) : ℝ :=
  if M < p then 0 else if p ∈ S then F * m * (1 + vd p / 2) * Mb + Sm
  else if p ∈ R then (F * N * Mb + Sm) / ((p : ℝ) - 1)
  else if m * p < k then eSmall F N m Mb Sm M p + 1 else (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1

example (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (S R : Finset ℕ) : eOf F N k m Mb Sm vd 3 S R 5 = 0 := by simp [eOf]

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def WtAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  Shape (dat p i) D.R.f D.R.k D.R.m ∧ D.R.k ≤ (dat p i).p + 1 ∧ ∃ (B : ℕ) (Sg : ℝ), WtBd (dat p i) D.R.k (nCol (dat p i)) u1 B Sg ∧
    lenT p i PP * ((B : ℝ) + 1) ≤ C * L.sc.b ∧ lenT p i PP * Sg ≤ C * L.sc.b ∧ 1 ≤ lenT p i PP

def NumAt (PP C : ℝ) : Prop :=
  1 ≤ L.sc.L ∧ 1 ≤ L.sc.b ∧ Real.log L.sc.b ≤ C * L.sc.L ∧ 1 ≤ Real.log (Real.log L.sc.x) ∧
    D.R.f * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) ≤ C * unitE p ∧
    Real.log (Real.log D.R.k) ≤ C * Real.log (Real.log L.sc.x) ∧ Real.log D.R.r ≤ C * L.sc.L ∧ Formalism.MainNotions.DIV.Cons.vd2 D ≤ C * L.sc.L ∧
    lenT p i PP * (D.R.r : ℝ) ^ 3 ≤ C * L.sc.b ∧
    ∀ q ∈ ({D.host.q, D.host.d} : Finset ℕ), D.R.r * Real.log q / ((q : ℝ) - 1) ≤ C * D.R.m * L.sc.L

end Point

def WtPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → WtAt p i PP C u1

def NumPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → NumAt p i PP C

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FactorDepth

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ}

def PolyBetween (la : PointsOfFlagModel.abelian₂ p c) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
    ∀ (Ch : IntegralChartA3 Xo c T io y) (k : ℕ),
      (A : EReal) ≤ nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ∧
        nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ≤ (B : EReal)

variable (l) in

def HalfSplit (g g' : ℕ) (π π' : 𝓞 E) : Prop :=
  g.Prime ∧ g'.Prime ∧ g ≠ g' ∧ l.M = g' * g ∧ π * H.bar π = (g : 𝓞 E) ∧ π' * H.bar π' = (g' : 𝓞 E) ∧
    l.Mb = Ideal.span {π * π'} ∧ GlobalTheory.PtTie.SplitsIn E g ∧ GlobalTheory.PtTie.SplitsIn E g'

theorem HalfSplit.symm {g g' : ℕ} {π π' : 𝓞 E} (h : HalfSplit l g g' π π') : HalfSplit l g' g π' π := by
  obtain ⟨a, b, c, d, e, f, i, j, k⟩ := h
  exact ⟨b, a, c.symm, d.trans (mul_comm _ _), f, e, by rw [i, mul_comm], k, j⟩

theorem PolyBetween.mono {la : PointsOfFlagModel.abelian₂ p c} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F} {A B A' B' : ℝ}
    (h : PolyBetween Xo la P A B) (hA : A' ≤ A) (hB : B ≤ B') : PolyBetween Xo la P A' B' :=
  fun T io e ho y hy Ch k => ⟨(EReal.coe_le_coe_iff.2 hA).trans (h T io e ho y hy Ch k).1,
    (h T io e ho y hy Ch k).2.trans (EReal.coe_le_coe_iff.2 hB)⟩

end Free

def JetNum (D : D7) (dF : ℕ) (cst : ℝ) : Prop :=
  ∀ k, 4 * dF + 4 ≤ D.host.g k ∧ (dF : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < D.host.g k ∧
    GlobalTheory.PtTie.rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (dF : ℝ) ^ 2) / D.host.g k ≤ cst

theorem JetNum.mono {D : D7} {dF : ℕ} {cst cst' : ℝ} (h : JetNum D dF cst) (hc : cst ≤ cst') : JetNum D dF cst' :=
  fun k => ⟨(h k).1, (h k).2.1, (h k).2.2.trans hc⟩

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SecSpaceBotNeBot
section
noncomputable section

open scoped TensorProduct NNReal Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWInt.Model

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

open Classical in

def ind (w g : UA σ J₂) (𝓓 : Set (unipN σ J₂)) (y : UA σ J₂) : ℂ := if ∃ x ∈ 𝓓, y = w * (x : UA σ J₂) * g then 1 else 0

omit [NumberField E] in

theorem ind_apply (w g : UA σ J₂) (𝓓 : Set (unipN σ J₂)) :
    (fun x : unipN σ J₂ => ind w g 𝓓 (w * x * g)) = 𝓓.indicator fun _ => 1 := by
  funext x
  by_cases h : x ∈ 𝓓
  · rw [Set.indicator_of_mem h, ind, if_pos ⟨x, h, rfl⟩]
  · rw [Set.indicator_of_notMem h, ind, if_neg]
    rintro ⟨y, hy, e⟩
    exact h ((Subtype.ext (mul_left_cancel (mul_right_cancel e)) : x = y) ▸ hy)

omit [NumberField E] in

theorem exists_intM_eq_one {νN : Measure (unipN σ J₂)} (h : IsNormN σ νN) (w g : UA σ J₂) :
    ∃ f, IntConv νN w f g ∧ intM νN w f g = 1 := by
  obtain ⟨-, 𝓓, h1, h2⟩ := h
  refine ⟨ind w g 𝓓, ?_, ?_⟩
  · rw [IntConv, ind_apply]
    exact (integrableOn_const (by rw [h2]; exact ENNReal.one_ne_top) : IntegrableOn (fun _ => (1 : ℂ)) 𝓓 νN).integrable_indicator₀
      h1.nullMeasurableSet
  · rw [intM, ind_apply, integral_indicator₀ h1.nullMeasurableSet, setIntegral_const, Measure.real, h2,
      ENNReal.toReal_one, one_smul]

omit [NumberField E] in

theorem coefM_pole {νN : Measure (unipN σ J₂)} {w : UA σ J₂} {f : UA σ J₂ → ℂ} (hf : ∀ g, IntConv νN w f g) :
    HasIntCont νN w (fun s => s⁻¹ • f) ∧ (∀ g, coefM νN w (fun s => s⁻¹ • f) 0 (-1) g = intM νN w f g) ∧
      (∀ g, contM νN w (fun s => s⁻¹ • f) 0 g = 0) ∧ ∀ g, contM νN w (fun s => s⁻¹ • f) (-1) g = -intM νN w f g := by
  have hm : ∀ g s, MeromorphicAt (fun s : ℂ => s⁻¹ * intM νN w f g) s := fun g s =>
    (MeromorphicAt.id s).inv.mul (.const _ _)
  have he : ∀ g, (fun s : ℂ => intM νN w (s⁻¹ • f) g) = fun s => s⁻¹ * intM νN w f g := fun g =>
    funext fun s => intM_smul _ _ _
  have hx : ∀ g, Cont.IsMerExt (fun s : ℂ => s⁻¹ * intM νN w f g) Set.univ fun s => s⁻¹ * intM νN w f g := fun g =>
    Cont.isMerExt_self Cont.isRightDomain_univ fun s _ => hm g s
  refine ⟨⟨⟨0, fun s _ g => (hf g).smul _⟩, fun g => ?_⟩, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · rw [he]; exact ⟨_, hx g⟩
  · rw [coefM, he]
    refine Cont.CoeffAt.laurent_eq (((hx g).isExtAt trivial).coeffAt_of_tendsto (k := 1) ?_)
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have : s ≠ 0 := hs
    simp only [sub_zero, pow_one]
    field_simp
  · rw [contM, he]
    refine Cont.ValueAt.cont_eq ⟨_, (hx g).isExtAt trivial, Polynomial.C (intM νN w f g) * Polynomial.X, by simp, ?_⟩
    refine tendsto_const_nhds.congr fun s => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, sub_zero, mul_comm, sub_self]
  · rw [contM, he]
    refine Cont.ValueAt.cont_eq (Cont.HolValueAt.valueAt ⟨_, (hx g).isExtAt trivial, ?_, by simp⟩)
    exact (analyticAt_id.inv (by simp)).mul analyticAt_const

omit [NumberField E] in

theorem exists_ratN (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (c : ℕ) :
    ∃ u : ratN σ J₂, inBasis σ T ((u : unipN σ J₂) : UA σ J₂) = blk 1 (c • 1) 0 1 := by
  have hG := WittModel.gram_of_isWittBasis hσ hl hJ h
  rw [← h₂] at hG
  have hm : (blk 1 (c • 1) 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) E) * blk 1 (-(c • 1)) 0 1 = 1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]; simp
  let w₀ : GL (Fin (n + n)) E := ⟨_, _, hm, mul_eq_one_comm.1 hm⟩
  have mp : ∀ {S : Type} [CommRing S] (f : E →+* S),
      (blk 1 (c • 1) 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) E).map f = blk 1 (c • 1) 0 1 := fun f => by
    have : (c • (1 : Matrix (Fin n) (Fin n) E)).map f = c • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.one_apply, apply_ite f, map_one, map_zero]
    simp only [blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f), this,
      Matrix.map_zero _ (map_zero f)]
  have hw : w₀.1ᵀ * blk 0 1 (-1) 0 * w₀.1.map σ = blk 0 1 (-1) 0 := by
    have e : w₀.1ᵀ = blk 1 0 (c • 1) 1 := by
      simp only [w₀, blk, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_one,
        Matrix.transpose_smul, Matrix.transpose_zero]
    have e' : w₀.1.map σ = blk 1 (c • 1) 0 1 := mp (σ : E →+* E)
    rw [e, e', WittModel.blk_mul, WittModel.blk_mul]
    simp
  have hT : T.1ᵀ * J₂ * T.1.map σ = l • blk 0 1 (-1) 0 := by
    rw [← hG, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl, one_smul]
  have i1 : (T⁻¹).1ᵀ * T.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have i2 : T.1.map σ * (T⁻¹).1.map σ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have key : (T * w₀ * T⁻¹).1ᵀ * J₂ * (T * w₀ * T⁻¹).1.map σ = J₂ := by
    calc _ = (T⁻¹).1ᵀ * (w₀.1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * w₀.1.map σ) * (T⁻¹).1.map σ := by
          simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = (T⁻¹).1ᵀ * (T.1ᵀ * J₂ * T.1.map σ) * (T⁻¹).1.map σ := by
          rw [hT, Matrix.mul_smul, Matrix.smul_mul, hw]
      _ = ((T⁻¹).1ᵀ * T.1ᵀ) * J₂ * (T.1.map σ * (T⁻¹).1.map σ) := by simp only [Matrix.mul_assoc]
      _ = J₂ := by rw [i1, i2, Matrix.one_mul, Matrix.mul_one]
  have hU : Matrix.GeneralLinearGroup.map (inclR (AF F)) (T * w₀ * T⁻¹) ∈ UG (cA σ) (incM F J₂) := by
    have := congrArg (fun X => incM F X) key
    simp only [incM, Matrix.map_mul, Matrix.transpose_map] at this
    refine Eq.trans ?_ this
    congr 1
  let u : UA σ J₂ := ⟨_, hU⟩
  have hu : inBasis σ T u = blk 1 (c • 1) 0 1 := by
    change incM F (T⁻¹).1 * incM F (T * w₀ * T⁻¹).1 * incM F T.1 = _
    rw [incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul,
      show T⁻¹ * (T * w₀ * T⁻¹) * T = w₀ by group]
    exact mp _
  have hN : u ∈ unipN σ J₂ := by
    obtain ⟨Z, -, hZ⟩ := h
    have hT' : incM F T.1 = blk 1 (incM F Z) 1 (-incM F Z) := by
      simp only [hZ, incM, blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]
    have hc : ∀ a b c d x y : Matrix (Fin n) (Fin n) (AE F E), blk a b c d * blockColumnMatrix x y = blockColumnMatrix (a * x + b * y) (c * x + d * y) :=
      fun a b c d x y => by
        rw [blk, blockColumnMatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows, blockColumnMatrix]
    have e1 : blockColumnMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) 1 = incM F T.1 * blockColumnMatrix 1 0 := by rw [hT']; erw [hc]; simp
    have e2 : mat u * incM F T.1 = incM F T.1 * blk 1 (c • 1) 0 1 := by
      rw [← hu, inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]
    rw [mem_unipN_iff, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, e1]
    erw [← Matrix.mul_assoc, e2, Matrix.mul_assoc, hc]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    rfl
  exact ⟨⟨⟨u, hN⟩, ⟨_, rfl⟩⟩, hu⟩

omit [NumberField E] in

theorem infinite_ratN (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (hn : 1 ≤ n) : Infinite (ratN σ J₂) := by
  choose u hu using exists_ratN hσ hl hJ h₂ h
  refine Infinite.of_injective u fun a b e => ?_
  have h1 := (hu a).symm.trans ((congrArg (fun x : ratN σ J₂ => inBasis σ T ((x : unipN σ J₂) : UA σ J₂)) e).trans (hu b))
  have h2 := congrFun (congrFun h1 (finSumFinEquiv (.inl ⟨0, hn⟩))) (finSumFinEquiv (.inr ⟨0, hn⟩))
  simp only [blk, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
    Matrix.one_apply_eq] at h2
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at h2
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AE F E) := inferInstanceAs (Nontrivial (AF F ⊗[F] E))
  haveI : CharZero (AE F E) := charZero_of_injective_algebraMap (algebraMap F (AE F E)).injective
  exact_mod_cast h2

theorem not_intConv_one (hcm : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) {T : GL (Fin (n + n)) E}
    (h : IsWittBasis σ J l T) (hn : 1 ≤ n) {νN : Measure (unipN σ J₂)} (hν : IsNormN σ νN) (w g : UA σ J₂) :
    ¬ IntConv νN w (fun _ => 1) g := by
  obtain ⟨h0, 𝓓, h1, h2⟩ := hν
  haveI := infinite_ratN (GlobalTheory.SiegelSet.sigma_sigma hcm) hl hJ h₂ h hn
  obtain ⟨hTG, -, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ J₂
  haveI : BorelSpace (UA σ J₂) := ⟨rfl⟩
  haveI : Countable (ratN σ J₂) := GlobalTheory.UnipMass.countable_ratU' σ J₂ (unipN σ J₂)
  haveI : MeasurableConstSMul (ratN σ J₂) (unipN σ J₂) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : unipN σ J₂ => (γ : unipN σ J₂) * x).measurable⟩
  haveI : SMulInvariantMeasure (ratN σ J₂) (unipN σ J₂) νN := ⟨fun γ A _ => measure_preimage_mul νN (γ : unipN σ J₂) A⟩
  intro hc
  have h3 := h1.measure_eq_tsum Set.univ
  simp only [Set.smul_set_univ, Set.univ_inter, h2, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at h3
  rcases integrable_const_iff.1 hc with h4 | h4
  · exact one_ne_zero h4
  · exact measure_ne_top νN _ h3

omit [NumberField E] in

theorem intM_rank_zero {J₂ : Matrix (Fin (0 + 0)) (Fin (0 + 0)) E} {νN : Measure (unipN σ J₂)} (hν : IsNormN σ νN)
    (w g : UA σ J₂) (f : UA σ J₂ → ℂ) : intM νN w f g = f g := by
  haveI : Subsingleton (UA σ J₂) := ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => i.elim0))⟩
  obtain ⟨-, 𝓓, -, h2⟩ := hν
  have hu : νN Set.univ = 1 := by
    rcases Set.eq_empty_or_nonempty 𝓓 with e | e
    · rw [e, measure_empty] at h2; exact absurd h2 zero_ne_one
    · rw [← h2, Subsingleton.eq_univ_of_nonempty e]
  rw [intM, show (fun x : unipN σ J₂ => f (w * x * g)) = fun _ => f g from funext fun _ => congrArg f (Subsingleton.elim _ _),
    integral_const, Measure.real, hu, ENNReal.toReal_one, one_smul]

omit [NumberField E] in

theorem secSpace_bot_ne_bot {JV : Matrix (Fin m) (Fin m) E} {κ : Type} [Fintype κ]
    (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) : secSpace om ⊥ ≠ ⊥ := by
  obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  refine (Submodule.ne_bot_iff _).2 ⟨_, mem_secSpace.2 ⟨φ, h, (kFin_iff om ⊥ φ).2 ⟨ℂ ∙ φ, inferInstance, fun k hk => ?_⟩, rfl⟩,
    fun e => h0 ?_⟩
  · rw [Subgroup.mem_bot.1 hk, Prod.mk_one_one, map_one]; exact Submodule.mem_span_singleton_self φ
  · have := congrFun e 1
    rwa [Prod.mk_one_one, map_one] at this

theorem exists_case : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J₂ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) E) (T : GL (Fin (2 + 2)) E) (w : UA σ J₂)
    (νN : Measure (unipN σ J₂)), ComplMet σ 1 1 False ∧ IsWeylElt σ T w ∧ IsNormN σ νN ∧
    w ∉ siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype ∧
    (∃ f, IntConv νN w f 1 ∧ intM νN w f 1 = 1) ∧ ¬ IntConv νN w (fun _ => 1) 1 := by
  obtain ⟨F, E, _, _, _, _, _, σ, h⟩ := exists_complMet
  obtain ⟨hcm, -, ψ, -, l, JV, J, J₂, hl, -, -, hJ, h₂, T, hT, χ, -, -, K, -, -, ⟨w, hw⟩, ⟨ν, hν⟩, -⟩ := h 1 1
  exact ⟨F, E, _, _, _, _, _, σ, J₂, T, w, ν, h 1 1, hw, hν, hw.not_mem_siegelOf hT (by norm_num), exists_intM_eq_one hν w 1,
    not_intConv_one hcm hl hJ h₂ hT (by norm_num) hν w 1⟩

end GlobalTheory.SWInt.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def eV0 (p : PtAt ex Csz) (t : Tup p) : (Fin ((Df p).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] p.P.A3.A.fam.amb.FR t :=
  ((p.P.A3.A.fam.R t).S.basis.equivFun.symm :
      (Fin (p.P.A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (p.P.A3.A.fam.R t).S.Forms) ∘ₗ
    ((p.P.A3.A.fam.R t).vE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)).mulVecLin

def InUse (p : PtAt ex Csz) (t : Tup p) : Prop := t = p.P.A3.A.μ0 ∨ ∃ w, p.R.mu w = t

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n)

def TieTest : Prop := IsTestLat d.G a.rp d.n a.e d.X' d.M

def TieV : Prop := ∀ t, InUse p t → ∀ (x : Fin ((Df p).nV t) → D.what₂.LL) (i : Fin d.n),
  D.what₂.embLL ((d.V t).mulVec x i) = vK a.ch t (eV0 p t x) i

def TieSq : Prop :=
  IsSqOf d.W a.S.B a.rm CF p.P.A3.A.μ0 p.R.mu d.rq d.zA d.zA' d.zT d.zTd d.gT d.ch d.N0 d.Sd d.Se d.dl d.Bw

structure TieAt : Prop where

  ok : a.OK

  test : TieTest d a

  sums : TieV d a

  sq : TieSq d a

def Comparison₂ : TieT := fun p _ d => ∃ a : SlopeTestRemainingChoices p d.G d.W d.n, TieAt d a

end GlobalTheory.BigTop.Fun

end
end

