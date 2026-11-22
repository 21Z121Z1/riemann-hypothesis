import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEmbeddingProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagAtOfFlagAt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.GradedPieces GlobalTheory.Points GlobalTheory.LieMet

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem inf_le_preimage (q q' : LatChart Z L) (hg : q.g = q'.g) : q.U ⊓ q'.U ≤ q.g ⁻¹ᵁ (q.V ⊓ q'.V) :=
  fun z hz => ⟨q.le hz.1, by rw [hg]; exact q'.le hz.2⟩

def pullInf (q q' : LatChart Z L) (hg : q.g = q'.g) : Γ(B.X, q.V ⊓ q'.V) →+* Γ(Z.X, q.U ⊓ q'.U) :=
  (q.g.appLE _ _ (inf_le_preimage q q' hg)).hom

def crd (q q' : LatChart Z L) (l : Fin q'.n) (j : Fin q.n) : Γ(B.X, q.V ⊓ q'.V) :=
  (q.frame.basis (inf_le_left : q.V ⊓ q'.V ≤ q.V)).repr (GlobalTheory.Twist.resM _ inf_le_right (q'.m l)) j

def crossC (q q' : LatChart Z L) (hg : q.g = q'.g) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (l : Fin q'.n) :
    Γ(Z.X, q.U ⊓ q'.U) :=
  ∑ j, pullInf q q' hg (crd q q' l j) * resG _ inf_le_left (q.c σ i j)

def extMat (q : LatChart Z L) (σ : E →+* ℂ) : GL (Fin q.n) Γ(Z.X, q.U) := (q.ext σ).choose

def extEmb (q : LatChart Z L) (σ : E →+* ℂ) : Fin (Dw.mult σ) ↪ Fin q.n := (q.ext σ).choose_spec.choose

theorem extMat_apply (q : LatChart Z L) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (l : Fin q.n) :
    (q.extMat σ : Matrix (Fin q.n) (Fin q.n) Γ(Z.X, q.U)) (q.extEmb σ i) l = q.c σ i l :=
  (q.ext σ).choose_spec.choose_spec i l

def diagFn (q q' : LatChart Z L) (hg : q.g = q'.g) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : Γ(Z.X, q.U ⊓ q'.U) :=
  ∑ l, crossC q q' hg σ i l *
    resG _ inf_le_right ((((q'.extMat σ)⁻¹ : GL (Fin q'.n) Γ(Z.X, q'.U)) : Matrix (Fin q'.n) (Fin q'.n) Γ(Z.X, q'.U))
      l (q'.extEmb σ i))

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem tanEv_sum_smul {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ j, a j • s j) = ∑ j, valR x V (a j) * tanEv t hv h (s j) := by
  let f : Γ(GlobalTheory.LieVB.omega t.G, V) →+ k := AddMonoidHom.mk' (tanEv t hv h) (tanEv_add t hv h)
  change f (∑ j, a j • s j) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change tanEv t hv h (a j • s j) = _
  rw [tanEv_smul, valR, dif_pos h]

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem valR_crossC (q q' : LatChart Z L) (hg : q.g = q'.g) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (hu : q.FrameAt x u) (hu' : q'.FrameAt x u') (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (cf : Fin (Dw.mult σ) → k) (hc : IsCombAtG (Y Z.i).t (x ≫ Z.π) (u' σ) cf (u σ i)) (l : Fin q'.n) :
    valR x (q.U ⊓ q'.U) (crossC q q' hg σ i l) = ∑ b, cf b * valR x q'.U (q'.c σ b l) := by
  obtain ⟨hU, hfl, hco⟩ := hu
  obtain ⟨hU', hfl', hco'⟩ := hu'
  rw [← hg] at hco'
  obtain ⟨τ, mu, hV, htr, hv⟩ := hco
  obtain ⟨τ', mu', hV', htr', hv'⟩ := hco'
  have hx : ⊤ ≤ x ⁻¹ᵁ (q.U ⊓ q'.U) := le_preimage_inf hU hU'
  obtain ⟨a, φ, hφ, hfr, -⟩ := hfl
  obtain ⟨a', φ', hφ', hfr', -⟩ := hfl'
  obtain ⟨y, hy, -⟩ := CommonMod.exists_lift_chart Z hφ
  obtain ⟨rfl, hmu⟩ := GlobalTheory.TransUniq.trans_unique E H Dw Xo p W Y B.i Z.i τ τ' mu mu' q.isMap.1.2.1 htr htr'
  have hmu' : ∀ w : Sp (DualNumber k) ⟶ (Y Z.i).t.G.left, IsTanAtG (Y Z.i).t (x ≫ Z.π) w → w ≫ mu.φ = w ≫ mu'.φ :=
    fun w hw => hmu k y _ (spMap (algebraMap k (DualNumber k))) w (by rw [hw.1, hy])
  have hxτ : (x ≫ Z.π) ≫ τ = (x ≫ q.g) ≫ B.π := by
    rw [Category.assoc, Category.assoc, CommonMod.comp_π_eq q.isMap htr]
  choose v hvt hve hvc using hv σ i
  choose v' hvt' hve' hvc' using hv' σ
  have hcomb : IsCombAtG B.t (x ≫ q.g) v' cf v :=
    StepBasis.isComb_corr mu B.tMap hxτ (fun b => (hfr'.1 σ b).1) hvt'
      (fun b => (hmu' _ (hfr'.1 σ b).1).trans (hve' b).symm) (hfr.1 σ i).1 hvt hve.symm hc
  have hVV : ⊤ ≤ (x ≫ q.g) ⁻¹ᵁ (q.V ⊓ q'.V) := le_preimage_inf hV hV'
  have key := GlobalTheory.LocM.tanEv_comb E H B.X B.t k (x ≫ q.g) _ hVV _ v' hvt' cf v hvt hcomb
    (L.N.incl.app (q.V ⊓ q'.V) (GlobalTheory.Twist.resM _ inf_le_right (q'.m l)))
  have rhs : ∀ b, tanEv B.t (hvt' b) hVV (L.N.incl.app (q.V ⊓ q'.V) (GlobalTheory.Twist.resM _ inf_le_right (q'.m l))) =
      valR x q'.U (q'.c σ b l) := fun b => by
    rw [GlobalTheory.Twist.app_resM, tanEv_resM]
    exact hvc' b l
  have e : GlobalTheory.Twist.resM _ inf_le_right (q'.m l) =
      ∑ j, crd q q' l j • GlobalTheory.Twist.resM _ (inf_le_left : q.V ⊓ q'.V ≤ q.V) (q.m j) := by
    refine ((q.frame.basis inf_le_left).sum_repr _).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [GlobalTheory.VB.IsFrame.basis_apply]
    rfl
  have lhs : tanEv B.t hvt hVV (L.N.incl.app (q.V ⊓ q'.V) (GlobalTheory.Twist.resM _ inf_le_right (q'.m l))) =
      ∑ j, valR (x ≫ q.g) _ (crd q q' l j) * valR x q.U (q.c σ i j) := by
    rw [e, map_sum]
    simp only [Scheme.Modules.Hom.app_smul]
    rw [tanEv_sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Twist.app_resM, tanEv_resM]
    exact congrArg _ (hvc j)
  have hval : valR x (q.U ⊓ q'.U) (crossC q q' hg σ i l) =
      ∑ j, valR (x ≫ q.g) _ (crd q q' l j) * valR x q.U (q.c σ i j) := by
    rw [crossC, valR_eq x _ hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← valR_eq x _ hx, ← valR_eq x _ hx, pullInf, valR_appLE x q.g _ hx, valR_res x _ hx]
  rw [hval, ← lhs, key]
  exact Finset.sum_congr rfl fun b _ => by rw [rhs]

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem valR_diagFn (q q' : LatChart Z L) (hg : q.g = q'.g) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (hu : q.FrameAt x u) (hu' : q'.FrameAt x u') (σ : E →+* ℂ)
    {d : Fin (Dw.mult σ) → k} (hd : DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) d) (i : Fin (Dw.mult σ)) :
    valR x (q.U ⊓ q'.U) (diagFn q q' hg σ i) = d i := by
  obtain ⟨cf, hci, -, hc⟩ := hd i
  have hx : ⊤ ≤ x ⁻¹ᵁ (q.U ⊓ q'.U) := le_preimage_inf hu.1 hu'.1
  have hx' : ⊤ ≤ x ⁻¹ᵁ q'.U := hu'.1
  have hone : ∀ b, ∑ l, valR x q'.U (q'.c σ b l) * valR x q'.U
      ((((q'.extMat σ)⁻¹ : GL (Fin q'.n) Γ(Z.X, q'.U)) : Matrix (Fin q'.n) (Fin q'.n) Γ(Z.X, q'.U)) l (q'.extEmb σ i)) =
        if b = i then 1 else 0 := fun b => by
    simp_rw [← extMat_apply, valR_eq x _ hx', ← map_mul, ← map_sum, ← Matrix.mul_apply]
    rw [Units.mul_inv, Matrix.one_apply]
    simp only [(q'.extEmb σ).injective.eq_iff]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [diagFn, valR_eq x _ hx, map_sum]
  simp_rw [map_mul, ← valR_eq x _ hx, valR_crossC q q' hg hu hu' σ i cf hc, valR_res x _ hx, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, hone, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact hci

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem exists_diagAt_of_flagAt (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) (h' : Z.FlagAt x u') (σ : E →+* ℂ) :
    ∃ d, DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) d := by
  obtain ⟨_, _, _, hf, _⟩ := id h
  obtain ⟨_, _, _, hf', _⟩ := id h'
  obtain ⟨d, hd⟩ := exists_diag_of_flagAt Z hty h h' σ (fun i => (hf.1 σ i).1) (fun i => (hf'.1 σ i).1)
    (FJ.FlagIndep.linInd_of_frame hf' σ)
  exact ⟨d, (diagAt_iff _ _ d).2 hd⟩

theorem diag_mul_eq_one {k : Type} [Field k] {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u)
    (h' : Z.FlagAt x u') {σ : E →+* ℂ} {d d' : Fin (Dw.mult σ) → k}
    (hd : DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) d) (hd' : DiagAt (Y Z.i).t (x ≫ Z.π) (u σ) (u' σ) d')
    (a : Fin (Dw.mult σ)) : d a * d' a = 1 := by
  obtain ⟨_, _, _, hf, _⟩ := h
  obtain ⟨_, _, _, hf', _⟩ := h'
  have t1 := (diagAt_iff (fun i => (hf.1 σ i).1) (fun i => (hf'.1 σ i).1) d').1 hd'
  have t2 := (diagAt_iff (fun i => (hf'.1 σ i).1) (fun i => (hf.1 σ i).1) d).1 hd
  exact congrFun ((t1.trans t2).unique (FJ.FlagIndep.linInd_of_frame hf σ) (Diag.refl _)) a

theorem isUnit_diagFn (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) (q q' : LatChart Z L) (hg : q.g = q'.g)
    (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : IsUnit (diagFn q q' hg σ a) := by
  refine IsUnit.of_mul_eq_one (resG _ (inf_comm q.U q'.U).le (diagFn q' q hg.symm σ a)) (fn_ext Z fun k _ x h ho => ?_)
  obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x inf_le_left h) ho
  obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x inf_le_right h) ho
  obtain ⟨d, hd⟩ := exists_diagAt_of_flagAt hty hu.2.1 hu'.2.1 σ
  obtain ⟨d', hd'⟩ := exists_diagAt_of_flagAt hty hu'.2.1 hu.2.1 σ
  rw [valR_mul x _ h, valR_res x _ h, valR_one x _ h, valR_diagFn q q' hg hu hu' σ hd a,
    valR_diagFn q' q hg.symm hu' hu σ hd' a]
  exact diag_mul_eq_one hu.2.1 hu'.2.1 hd hd' a

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

theorem existsUnique_isTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z B : Mdl Y i₀) (L : Lat B), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) →
    ∀ (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ), ∃! a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L hty q q' e
  have hg : q.g = q'.g := MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW Z B q.g q'.g q.isMap q'.isMap
  refine ⟨∏ σ, ∏ i, (isUnit_diagFn hty q q' hg σ i).unit ^ e σ i, fun k _ x u u' d hu hu' hd => ?_, fun b hb => ?_⟩
  · have hx : ⊤ ≤ x ⁻¹ᵁ (q.U ⊓ q'.U) := le_preimage_inf hu.1 hu'.1
    rw [valR_prod_zpow x hx]
    refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [IsUnit.unit_spec, valR_diagFn q q' hg hu hu' σ (hd σ) i]
  · refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
    obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x inf_le_left h) ho
    obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x inf_le_right h) ho
    choose d hd using fun σ => exists_diagAt_of_flagAt hty hu.2.1 hu'.2.1 σ
    rw [hb k x u u' d hu hu' hd, valR_prod_zpow x h]
    refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [IsUnit.unit_spec, valR_diagFn q q' hg hu hu' σ (hd σ) i]

end GlobalTheory.LocM.LatChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSquaresConeOfCompactPosDef
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

open Filter Topology

namespace GlobalTheory.ConeSq

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def sq (l : ι → ℤ) : Matrix ι ι ℝ := vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))

def cone (S : Finset (ι → ℤ)) : Set (Matrix ι ι ℝ) :=
  {P | ∃ c : (ι → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • sq l}

theorem zero_mem (S : Finset (ι → ℤ)) : (0 : Matrix ι ι ℝ) ∈ cone S :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem add_mem {S : Finset (ι → ℤ)} {P Q : Matrix ι ι ℝ} (hP : P ∈ cone S) (hQ : Q ∈ cone S) :
    P + Q ∈ cone S := by
  obtain ⟨c, hc, rfl⟩ := hP
  obtain ⟨d, hd, rfl⟩ := hQ
  exact ⟨c + d, fun l => add_nonneg (hc l) (hd l), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem smul_mem {S : Finset (ι → ℤ)} {P : Matrix ι ι ℝ} {a : ℝ} (ha : 0 ≤ a) (hP : P ∈ cone S) :
    a • P ∈ cone S := by
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨a • c, fun l => mul_nonneg ha (hc l), by simp [Finset.smul_sum, smul_smul]⟩

theorem mono {S T : Finset (ι → ℤ)} (h : S ⊆ T) {P : Matrix ι ι ℝ} (hP : P ∈ cone S) :
    P ∈ cone T := by
  obtain ⟨c, hc, rfl⟩ := hP
  refine ⟨fun l => if l ∈ S then c l else 0, fun l => by dsimp only; split_ifs <;> simp [hc], ?_⟩
  rw [← Finset.sum_subset h (fun l _ hl => by simp [hl])]
  exact Finset.sum_congr rfl fun l hl => by simp [hl]

theorem sq_mem {S : Finset (ι → ℤ)} {l : ι → ℤ} (hl : l ∈ S) : sq l ∈ cone S := by
  refine ⟨fun m => if m = l then 1 else 0, fun m => by dsimp only; split_ifs <;> norm_num, ?_⟩
  rw [Finset.sum_eq_single l (fun m _ hm => by simp [hm]) (fun h => absurd hl h)]
  simp

theorem sum_mem {S : Finset (ι → ℤ)} {κ : Type} (s : Finset κ) {f : κ → Matrix ι ι ℝ}
    (h : ∀ k ∈ s, f k ∈ cone S) : ∑ k ∈ s, f k ∈ cone S :=
  Finset.sum_induction f (· ∈ cone S) (fun _ _ => add_mem) (zero_mem S) h

def plus (i j : ι) : ι → ℤ := Pi.single i 1 + Pi.single j 1

def minus (i j : ι) : ι → ℤ := Pi.single i 1 - Pi.single j 1

def gens : Finset (ι → ℤ) :=
  Finset.univ.image (fun p : ι × ι => plus p.1 p.2) ∪ Finset.univ.image (fun p : ι × ι => minus p.1 p.2)

def bsum : Matrix ι ι ℝ := ∑ p : ι × ι, (sq (plus p.1 p.2) + sq (minus p.1 p.2))

theorem sq_plus_sub_sq_minus (i j a b : ι) :
    sq (plus i j) a b - sq (minus i j) a b =
      2 * ((if a = i ∧ b = j then 1 else 0) + (if a = j ∧ b = i then 1 else 0)) := by
  simp only [sq, plus, minus, vecMulVec_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply,
    Int.cast_add, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rcases eq_or_ne i j with rfl | hij
  · by_cases h1 : a = i <;> by_cases h3 : b = i <;> simp [h1, h3] <;> norm_num
  · by_cases h1 : a = i <;> by_cases h2 : a = j <;> by_cases h3 : b = i <;> by_cases h4 : b = j <;>
      first
      | exact absurd (h1.symm.trans h2) hij
      | exact absurd (h3.symm.trans h4) hij
      | (simp [h1, h2, h3, h4, hij, hij.symm]; try norm_num)

theorem eq_sum_sq_sub (M : Matrix ι ι ℝ) (hM : ∀ a b, M a b = M b a) :
    M = ∑ p : ι × ι, (M p.1 p.2 / 4) • (sq (plus p.1 p.2) - sq (minus p.1 p.2)) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, sq_plus_sub_sq_minus]
  rw [Fintype.sum_prod_type]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [hM b a]; ring

theorem shift_mem (t : ℝ) (M : Matrix ι ι ℝ) (hM : ∀ a b, M a b = M b a)
    (hb : ∀ a b, |M a b| ≤ 4 * t) : t • bsum + M ∈ cone gens := by
  have e : t • bsum + M = ∑ p : ι × ι, ((t + M p.1 p.2 / 4) • sq (plus p.1 p.2)
      + (t - M p.1 p.2 / 4) • sq (minus p.1 p.2)) := by
    conv_lhs => rw [eq_sum_sq_sub M hM]
    rw [bsum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    module
  rw [e]
  refine sum_mem _ fun p _ => add_mem (smul_mem ?_ (sq_mem ?_)) (smul_mem ?_ (sq_mem ?_))
  · have := abs_le.mp (hb p.1 p.2); linarith
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  · have := abs_le.mp (hb p.1 p.2); linarith
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))

theorem sq_symm (l : ι → ℤ) (a b : ι) : sq l a b = sq l b a := by
  simp only [sq, vecMulVec_apply, mul_comm]

theorem bsum_symm (a b : ι) : (bsum : Matrix ι ι ℝ) a b = bsum b a := by
  simp only [bsum, Matrix.sum_apply, Matrix.add_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [sq_symm _ a b, sq_symm (minus p.1 p.2) a b]

theorem quad_eq (M : Matrix ι ι ℝ) (c : ι → ℝ) :
    star c ⬝ᵥ (M *ᵥ c) = ∑ i, ∑ j, c i * c j * M i j := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tendsto_floor_div (x : ℝ) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) * x⌋ : ℤ) : ℝ) / N) atTop (𝓝 x) := by
  have h1 : Tendsto (fun N : ℕ => x - 1 / (N : ℝ)) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    have := Int.lt_floor_add_one ((N : ℝ) * x)
    linarith [mul_comm x (N : ℝ)]
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [div_le_iff₀ hN']
    have := Int.floor_le ((N : ℝ) * x)
    linarith [mul_comm x (N : ℝ)]

open scoped MatrixOrder in

theorem local_step (P₀ : Matrix ι ι ℝ) (h : P₀.PosDef) :
    ∃ S : Finset (ι → ℤ), ∀ᶠ P in 𝓝 P₀, P.IsHermitian → P ∈ cone S := by
  have hP₀s : ∀ a b, P₀ a b = P₀ b a := fun a b => by
    have := h.isHermitian.apply a b
    rw [star_trivial] at this
    exact this.symm
  obtain ⟨η, hη, hmar⟩ := GlobalTheory.posDef_quad_margin (fun i j => P₀ i j) (fun c hc => by
    have := h.dotProduct_mulVec_pos hc
    rwa [quad_eq] at this)
  set β : ℝ := ∑ a, ∑ b, |(bsum : Matrix ι ι ℝ) a b| + 1 with hβdef
  have hβ : 0 < β := by positivity
  have hbβ : ∀ a b, |(bsum : Matrix ι ι ℝ) a b| ≤ β := fun a b => by
    have h1 : |(bsum : Matrix ι ι ℝ) a b| ≤ ∑ b', |(bsum : Matrix ι ι ℝ) a b'| :=
      Finset.single_le_sum (f := fun b' => |(bsum : Matrix ι ι ℝ) a b'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b', |(bsum : Matrix ι ι ℝ) a b'| ≤ ∑ a', ∑ b', |(bsum : Matrix ι ι ℝ) a' b'| :=
      Finset.single_le_sum (f := fun a' => ∑ b', |(bsum : Matrix ι ι ℝ) a' b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  set t : ℝ := η / (2 * β) with htdef
  have ht : 0 < t := by positivity
  set G : Matrix ι ι ℝ := P₀ - (2 * t) • bsum with hGdef
  have hGs : ∀ a b, G a b = G b a := fun a b => by
    simp only [hGdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hP₀s a b, bsum_symm a b]
  have hG : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨IsHermitian.ext fun a b => by rw [star_trivial, hGs], fun c => ?_⟩
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    rw [quad_eq]
    have := hmar (fun a b => -(2 * t) * bsum a b) (fun a b => by
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      calc 2 * t * |(bsum : Matrix ι ι ℝ) a b| ≤ 2 * t * β := by gcongr; exact hbβ a b
        _ = η := by rw [htdef]; field_simp) c hc
    refine this.le.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    simp only [hGdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  set R : Matrix ι ι ℝ := CFC.sqrt G with hRdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hRR : R * R = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  have hRs : ∀ a b, R a b = R b a := fun a b => by
    have := hR.isHermitian.apply a b
    rw [star_trivial] at this
    exact this.symm
  have hGsum : ∀ a b, G a b = ∑ k, R k a * R k b := fun a b => by
    rw [← hRR, mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hRs a k]
  have hconv : ∀ a b, Tendsto (fun N : ℕ => ∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N)) atTop (𝓝 (G a b)) := fun a b => by
    rw [hGsum]
    exact tendsto_finset_sum _ fun k _ => (tendsto_floor_div _).mul (tendsto_floor_div _)
  have hev : ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ a b, |∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N) - G a b| < t :=
    (eventually_gt_atTop 0).and (eventually_all.2 fun a => eventually_all.2 fun b =>
      (hconv a b).eventually (eventually_abs_sub_lt _ ht))
  obtain ⟨N, hN, hNt⟩ := hev.exists
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set m : ι → ι → ℤ := fun k a => ⌊(N : ℝ) * R k a⌋ with hmdef
  set Q : Matrix ι ι ℝ := ∑ k, (1 / (N : ℝ) ^ 2) • sq (m k) with hQdef
  have hQ : ∀ a b, Q a b = ∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N) := fun a b => by
    simp only [hQdef, hmdef, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sq, vecMulVec_apply]
    exact Finset.sum_congr rfl fun k _ => by field_simp
  have hQs : ∀ a b, Q a b = Q b a := fun a b => by
    rw [hQ, hQ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hQmem : Q ∈ cone (Finset.univ.image m) :=
    sum_mem _ fun k _ => smul_mem (by positivity) (sq_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  refine ⟨gens ∪ Finset.univ.image m, ?_⟩
  have hnear : ∀ᶠ P in 𝓝 P₀, ∀ a b, |P a b - P₀ a b| < t :=
    eventually_all.2 fun a => eventually_all.2 fun b =>
      ((continuous_id.matrix_elem a b).tendsto P₀).eventually (eventually_abs_sub_lt _ ht)
  filter_upwards [hnear] with P hP hPh
  have hPs : ∀ a b, P a b = P b a := fun a b => by
    have := hPh.apply a b
    rw [star_trivial] at this
    exact this.symm
  set M : Matrix ι ι ℝ := (P - P₀) + (G - Q) with hMdef
  have e : P = Q + ((2 * t) • bsum + M) := by
    rw [hMdef, hGdef]; abel
  rw [e]
  refine add_mem (mono Finset.subset_union_right hQmem)
    (mono Finset.subset_union_left (shift_mem _ M ?_ ?_))
  · intro a b
    simp only [hMdef, Matrix.add_apply, Matrix.sub_apply]
    rw [hPs a b, hP₀s a b, hGs a b, hQs a b]
  · intro a b
    have h1 := hP a b
    have h2 := hNt a b
    rw [← hQ] at h2
    simp only [hMdef, Matrix.add_apply, Matrix.sub_apply]
    have h3 := abs_add_le (P a b - P₀ a b) (G a b - Q a b)
    rw [abs_sub_comm (G a b)] at h3
    linarith

theorem exists_finset_cone : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (𝒦 : Set (Matrix ι ι ℝ)),
    IsCompact 𝒦 → (∀ P ∈ 𝒦, P.PosDef) → ∃ S : Finset (ι → ℤ), ∀ P ∈ 𝒦, ∃ c : (ι → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro ι _ _ 𝒦 hK hpd
  choose S hS using fun P (hP : P ∈ 𝒦) => local_step P (hpd P hP)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover'
    (fun P hP => {Q : Matrix ι ι ℝ | Q.IsHermitian → Q ∈ cone (S P hP)}) hS
  refine ⟨t.biUnion (fun x => S x.1 x.2), fun P hP => ?_⟩
  obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.mp (ht hP)
  exact mono (Finset.subset_biUnion_of_mem _ hx) (hPx (hpd P hP).isHermitian)

end GlobalTheory.ConeSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatChartTop
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext isTan_map)
open GlobalTheory.LocM.StepBasis GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.LocM.TopChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem tanEv_map {X : Scheme.{0}} {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {V : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') (h' : ⊤ ≤ x' ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t (isTan_map φ hx hv) h' s = φ (tanEv t hv h s) := by
  subst hx
  exact GlobalTheory.LocM.tanEv_baseChange E H X t S x V h v hv T φ _ h' s

end GlobalTheory.LocM.TopChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStepStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_coordinates_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X), IsMap Z t.B g → ∃ D : LCrd (Y Z.i) Z.π, IsLat t Z g D := by
  first | exact @GlobalTheory.GrCl.exists_lCrd_isLat | exact GlobalTheory.GrCl.exists_lCrd_isLat | (intros; apply GlobalTheory.GrCl.exists_lCrd_isLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEmbeddingProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_embedding_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp O) (t : SAB H X), IsProjOver s → ∃ (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd := by
  first | exact @GlobalTheory.LieEmb.exists_isLieEmb | exact GlobalTheory.LieEmb.exists_isLieEmb | (intros; apply GlobalTheory.LieEmb.exists_isLieEmb <;> assumption)
end

