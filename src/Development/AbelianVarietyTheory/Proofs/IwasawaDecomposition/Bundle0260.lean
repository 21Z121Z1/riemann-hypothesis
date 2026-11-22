import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.CoefModB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

open Classical in

def twist (τ : E →+* ℂ) : ℂ →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then RingHom.id ℂ else starRingEnd ℂ

theorem twist_twist (τ : E →+* ℂ) (z : ℂ) : twist τ (twist τ z) = z := by
  unfold twist; split_ifs <;> simp

theorem twist_star (τ : E →+* ℂ) (z : ℂ) : twist τ (star z) = star (twist τ z) := by
  unfold twist; split_ifs <;> simp

theorem continuous_twist (τ : E →+* ℂ) : Continuous (twist τ) := by
  unfold twist; split_ifs
  · exact continuous_id
  · exact Complex.continuous_conj

theorem twist_embedding (w : InfinitePlace E) : twist w.embedding = RingHom.id ℂ := by
  unfold twist; rw [if_pos (by rw [InfinitePlace.mk_embedding])]

theorem coord_eq (τ : E →+* ℂ) (z : Cinf E) : coord τ z = twist τ (z (InfinitePlace.mk τ)) := by
  unfold coord twist; split_ifs <;> rfl

open Classical in
theorem atEmb_apply (τ : E →+* ℂ) (z : ℂ) (w : InfinitePlace E) :
    atEmb τ z w = if w = InfinitePlace.mk τ then twist τ z else 0 := by
  unfold atEmb twist
  rw [Pi.single_apply]
  split_ifs <;> simp_all

def sN (τ : E →+* ℂ) : ℂ →ₙ+* Cinf E where
  toFun := atEmb τ
  map_mul' z z' := (atEmb_mul τ z z').symm
  map_zero' := funext fun w => by classical simp [atEmb_apply]
  map_add' z z' := funext fun w => by
    classical
    simp only [atEmb_apply, Pi.add_apply]
    split_ifs <;> simp

theorem sN_apply (τ : E →+* ℂ) (z : ℂ) : sN τ z = atEmb τ z := rfl

theorem continuous_sN (τ : E →+* ℂ) : Continuous (sN τ) := by
  classical
  refine continuous_pi fun w => ?_
  simp only [sN_apply, atEmb_apply]
  split_ifs
  · exact continuous_twist τ
  · exact continuous_const

def yG (τ : E →+* ℂ) : GL (Fin n) ℂ →* GL (Fin n) (Cinf E) := cornerGL n (sN τ)

open Classical in
theorem yG_apply (τ : E →+* ℂ) (g : GL (Fin n) ℂ) (i j : Fin n) (w : InfinitePlace E) :
    (yG τ g).val i j w =
      if w = InfinitePlace.mk τ then twist τ (g.val i j) else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  change (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j w - sN τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) w +
    sN τ (g.val i j) w = _
  simp only [sN_apply, atEmb_apply, Matrix.one_apply]
  split_ifs <;> simp_all

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cEmb_mem (τ : E →+* ℂ) (x : UA E n) : (cEmb τ x).val ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 := congrArg (RingHom.mapMatrix ((coord τ).comp (pInf E))) hx
  rw [mul_one, map_mul, map_one] at h1
  rw [Matrix.mem_unitaryGroup_iff', ← h1]
  congr 1
  ext i j
  exact (GlobalTheory.DefiniteBC.coord_conjAd τ _).symm

theorem cEmb_infGL (τ' : E →+* ℂ) (y : GL (Fin n) (Cinf E)) (h : infGL E n y ∈ UA E n) (i j : Fin n) :
    (cEmb τ' ⟨_, h⟩).val i j = coord τ' (y.val i j) := by
  have e : cEmb τ' ⟨_, h⟩ = GeneralLinearGroup.map (coord τ') y := by
    change GeneralLinearGroup.map (coord τ') (GeneralLinearGroup.map (pInf E) (infGL E n y)) = _
    rw [pInf_infGL]
  rw [e]
  rfl

theorem yG_unitary (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (yG τ (GlobalTheory.Branching.unitaryIncl n u)).valᴴ * (yG τ (GlobalTheory.Branching.unitaryIncl n u)).val = 1 := by
  classical
  have hu : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  refine Matrix.ext fun i j => funext fun w => ?_
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply, yG_apply]
  split_ifs with hw
  · have h2 := congrFun₂ hu i j
    simp only [Matrix.mul_apply, Matrix.star_apply] at h2
    simp only [← twist_star, ← map_mul, ← map_sum]
    change twist τ (∑ k, star ((u : Matrix (Fin n) (Fin n) ℂ) k i) * (u : Matrix (Fin n) (Fin n) ℂ) k j) = _
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · by_cases h : i = j
    · subst h; simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h, Ne.symm h]

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem infGL_yG_mem_UA (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)) ∈ UA E n :=
  infGL_mem_UA _ (yG_unitary τ u)

theorem twist_one_apply (τ : E →+* ℂ) (i j : Fin n) :
    twist τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem mem_embU (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (⟨_, infGL_yG_mem_UA τ u⟩ : UA E n) ∈ embU n τ := by
  classical
  refine ⟨pFin_infGL _, ?_⟩
  refine Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [cEmb_infGL, coord_eq, yG_apply, if_neg h, twist_one_apply]
  rfl

def inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : embU n τ :=
  ⟨⟨_, infGL_yG_mem_UA τ u⟩, mem_embU τ u⟩

def fwd (τ : E →+* ℂ) (x : embU n τ) : Matrix.unitaryGroup (Fin n) ℂ := ⟨(cEmb τ x.1).val, cEmb_mem τ x.1⟩

theorem fwd_inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : fwd τ (inv τ u) = u := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change (cEmb τ ⟨_, infGL_yG_mem_UA τ u⟩).val i j = _
  rw [cEmb_infGL, coord_eq, yG_apply, if_pos rfl, twist_twist]
  rfl

theorem inv_fwd (τ : E →+* ℂ) (x : embU n τ) : inv τ (fwd τ x) = x := by
  classical
  have hx := Subgroup.mem_inf.1 x.2
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · change GeneralLinearGroup.map (pInf E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    rw [yG_apply]
    split_ifs with hw
    · subst hw
      change twist τ (coord τ (pInf E (x.1.1.val i j))) = _
      rw [coord_eq, twist_twist]
      rfl
    · have h1 : InfinitePlace.mk w.embedding ≠ InfinitePlace.mk τ := by
        rw [InfinitePlace.mk_embedding]; exact hw
      have hk := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) h1)
      have h2 := congrArg (fun g : GL (Fin n) ℂ => g.val i j) hk
      change coord w.embedding (pInf E (x.1.1.val i j)) = _ at h2
      rw [coord_eq, twist_embedding, InfinitePlace.mk_embedding] at h2
      exact h2.symm
  · change GeneralLinearGroup.map (pFin E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pFin_infGL]
    exact (MonoidHom.mem_ker.1 hx.1).symm

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  have : (coord τ : Cinf E → ℂ) = fun z => twist τ (z (InfinitePlace.mk τ)) := funext (coord_eq τ)
  rw [this]
  exact (continuous_twist τ).comp (continuous_apply _)

theorem continuous_fwd (τ : E →+* ℂ) : Continuous (fwd τ : embU n τ → Matrix.unitaryGroup (Fin n) ℂ) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun x : embU n τ => (x.1.1.val).map (fun a => coord τ (pInf E a))
  exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_map
    ((continuous_coord τ).comp continuous_pInf')

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

def phi (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (Ad E) :=
  corner (matN n (sInf E)) (corner (matN n (sN τ)) M)

theorem continuous_phi (τ : E →+* ℂ) : Continuous (phi (n := n) τ) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) ℂ => 1 - matN n (sInf E) 1 +
    (1 - matN n (sN τ) 1 + M.map (sN τ)).map (sInf E)
  exact continuous_const.add ((continuous_const.add (continuous_id.matrix_map (continuous_sN τ))).matrix_map
    continuous_sInf)

theorem continuous_inv (τ : E →+* ℂ) : Continuous (inv τ : Matrix.unitaryGroup (Fin n) ℂ → embU n τ) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => phi τ (u : Matrix (Fin n) (Fin n) ℂ)
    exact (continuous_phi τ).comp continuous_subtype_val
  · have e : ∀ u : Matrix.unitaryGroup (Fin n) ℂ,
        ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val =
          phi τ (star (u : Matrix (Fin n) (Fin n) ℂ)) := fun u => by
      rw [← map_inv, ← map_inv]
      rfl
    change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ =>
      ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val
    simp only [e]
    exact (continuous_phi τ).comp (continuous_star.comp continuous_subtype_val)

def equiv (τ : E →+* ℂ) : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ where
  toFun := fwd τ
  invFun := inv τ
  left_inv := inv_fwd τ
  right_inv := fwd_inv τ
  map_mul' x y := Subtype.ext (by
    change (cEmb τ (x.1 * y.1)).val = (cEmb τ x.1).val * (cEmb τ y.1).val
    rw [map_mul]
    rfl)
  continuous_toFun := continuous_fwd τ
  continuous_invFun := continuous_inv τ

theorem exists_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ,
      GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  intro E _ _ _ n τ
  exact ⟨equiv τ, fun x => Units.ext rfl⟩

end GlobalTheory.EmbUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
section
noncomputable section

namespace GlobalTheory.Mem.Col2.PerConj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix
open scoped ComplexOrder

section Val

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

def cev : Pol ℂ ι n →ₛₗ[starRingEnd ℂ] (Fr emb σ n → ℂ) := evFr (Gr emb σ n) (shiftOf lam) (starRingEnd ℂ)

theorem cev_injective : Function.Injective (cev emb σ lam) := evFr_injective _ _ _ (fr0 emb σ n)

theorem cev_mem {P : Pol ℂ ι n} (hP : P ∈ VV ℂ lam) : cev emb σ lam P ∈ ValC (Gr emb σ n) lam :=
  ⟨_, map_mem_CSpan (starRingEnd ℂ) lam P hP, rfl⟩

theorem exists_cev {z : Fr emb σ n → ℂ} (hz : z ∈ ValC (Gr emb σ n) lam) : ∃ P ∈ VV ℂ lam, cev emb σ lam P = z := by
  obtain ⟨p, hp, rfl⟩ := hz
  have h := CSpan_le_span (starRingEnd ℂ) lam hp
  clear hp
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, hP, rfl⟩ := hx
    exact ⟨P, hP, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, e⟩ := hx
    obtain ⟨Q, hQ, e'⟩ := hy
    exact ⟨P + Q, Submodule.add_mem _ hP hQ, by rw [map_add, map_add, e, e']⟩
  | smul r x _ hx =>
    obtain ⟨P, hP, e⟩ := hx
    exact ⟨starRingEnd ℂ r • P, Submodule.smul_mem _ _ hP, by rw [map_smulₛₗ, map_smul, e, Complex.conj_conj]⟩

theorem polOf_cev (P : Pol ℂ ι n) :
    polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (cev emb σ lam P) = MvPolynomial.map (starRingEnd ℂ) P := by
  have h := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (MvPolynomial.map (starRingEnd ℂ) P)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    exact inv_one
  rw [e] at h
  exact h

theorem nfAll_conj (p P : Pol ℂ ι n) : nfAll lam p (MvPolynomial.map (starRingEnd ℂ) P) = pairB lam p P := by
  have h1 := map_extNorm (RingHom.id ℂ) lam
  rw [RingHom.id_apply, pb_extNorm_eq] at h1
  rw [nfAll, ← h1, pairB_apply, div_eq_inv_mul]
  congr 1
  rw [fockF_eq_sum _ _ _ subset_rfl, fockB]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, starRingEnd_apply, star_star, mfact]

theorem ipVal_cev (P : Pol ℂ ι n) (w : Fr emb σ n → ℂ) :
    ipVal emb σ lam (cev emb σ lam P) w = pairB lam (polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) w) P := by
  rw [ipVal, ipFr_apply, polOf_cev, nfAll_conj]

theorem ipVal_pos {z : Fr emb σ n → ℂ} (hz : z ∈ ValC (Gr emb σ n) lam) (h0 : z ≠ 0) : 0 < ipVal emb σ lam z z := by
  obtain ⟨P, -, rfl⟩ := exists_cev emb σ lam hz
  rw [ipVal, ipFr_apply, polOf_cev, nfAll]
  have hP : MvPolynomial.map (starRingEnd ℂ) P ≠ 0 := by
    intro h
    apply h0
    have : P = 0 := MvPolynomial.map_injective _ (starRingEnd ℂ).injective (by rw [h, map_zero])
    rw [this, map_zero]
  exact div_pos (ps_fockF_pos _ hP)
    (Finset.prod_pos fun τ _ => ps_fockF_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))

theorem cev_act [StarRing E] (hE : ∀ τ x, embAt σ emb τ (star x) = starRingEnd ℂ (embAt σ emb τ x)) (γ : GL (Fin n) E)
    (hγ : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) (c : Kˣ) (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1)
    (P : Pol ℂ ι n) :
    cev emb σ lam ((σ (c : K))⁻¹ • rhoP lam (embGL (embAt σ emb) γ) P) = trFr emb σ γ c (cev emb σ lam P) := by
  have h1 : starRingEnd ℂ (σ (c : K))⁻¹ = σ c := by
    obtain ⟨m, hm, hc⟩ := hc
    have h2 : σ (c : K) ^ m = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
    have h3 : ‖σ (c : K)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hm.ne'
    rw [Complex.inv_eq_conj h3, Complex.conj_conj]
  have h4 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) E)ᴴ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hγ
  funext y
  rw [map_smulₛₗ, h1, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine (congrFun (evFr_actP (Gr emb σ n) (starRingEnd ℂ) lam (embGL (embAt σ emb) γ) P) y).trans ?_
  refine Eq.trans ?_ (fnOf_tr (G := Gr emb σ n) (G' := Gr emb σ n) (shiftOf lam) 1
    (fun τ => ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ))
    (MvPolynomial.map (starRingEnd ℂ) P) (frMul emb σ γ⁻¹ y) y fun _ => rfl).symm
  refine congrArg (fun M => fnOf (Gr emb σ n) (shiftOf lam) M (MvPolynomial.map (starRingEnd ℂ) P) y) ?_
  funext τ
  rw [h4, Pi.one_apply, Matrix.one_mul]
  ext a b
  exact (hE τ _).symm

end Val

section Per

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

def law (b : Q.S'.β) : Q.S'.G b →* Module.End ℂ (Pol ℂ ι (R.N R.m - 1)) where
  toFun g := (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (embAt σ emb) (Q.S'.gam b g))
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm, mul_inv]

def jM : Q.Mt emb σ →ₛₗ[starRingEnd ℂ] (Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) where
  toFun F c := cev emb σ Q.sgT (F.1 c.1 (Q.S'.rep c))
  map_add' F G := by
    funext c
    exact map_add (cev emb σ Q.sgT) _ _
  map_smul' r F := by
    funext c
    exact map_smulₛₗ (cev emb σ Q.sgT) r _

variable {Q}

theorem mt_law (hH : ∀ b, Q.H b = ⊤) (F : Q.Mt emb σ) (b : Q.S'.β) (g : Q.S'.G b) (d : Q.S'.D b) :
    F.1 b (g • d) = law Q emb σ b g (F.1 b d) :=
  (F.2 b d).2 g (by rw [hH]; trivial)

theorem jM_injective (hH : ∀ b, Q.H b = ⊤) : Function.Injective (jM Q emb σ) := by
  intro F G h
  apply Subtype.ext
  funext b d
  have h1 := cev_injective emb σ Q.sgT (congrFun h (Q.S'.cl b d))
  have h2 := mt_law emb σ hH F b (Q.S'.mv b d) (Q.S'.rep (Q.S'.cl b d))
  have h3 := mt_law emb σ hH G b (Q.S'.mv b d) (Q.S'.rep (Q.S'.cl b d))
  rw [Q.S'.mv_smul] at h2 h3
  rw [h2, h3]
  exact congrArg _ h1

variable (hE : ∀ τ x, embAt σ emb τ (star x) = starRingEnd ℂ (embAt σ emb τ x))
include hE

theorem cev_law (h : Q.Ok) (b : Q.S'.β) (g : Q.S'.G b) (P : Pol ℂ ι (R.N R.m - 1)) :
    cev emb σ Q.sgT (law Q emb σ b g P) = Q.S'.tr emb σ b g (cev emb σ Q.sgT P) :=
  cev_act emb σ Q.sgT hE _ (h.step.unit b g) _ (h.step.root b g) P

theorem jM_mem (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) (F : Q.Mt emb σ) : jM Q emb σ F ∈ Q.S'.Fi emb σ Q.sgT := by
  intro c
  refine ⟨cev_mem emb σ Q.sgT (F.2 c.1 (Q.S'.rep c)).1, fun g => ?_⟩
  have h2 := mt_law emb σ hH F c.1 g.1 (Q.S'.rep c)
  rw [g.2] at h2
  exact (cev_law emb σ hE h c.1 g.1 _).symm.trans (congrArg _ h2.symm)

theorem jM_onto (h : Q.Ok) (z : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (hz : z ∈ Q.S'.Fi emb σ Q.sgT) :
    ∃ F, jM Q emb σ F = z := by
  choose P hP hPz using fun c => exists_cev emb σ Q.sgT (hz c).1
  have hfix : ∀ b q (g : Q.S'.G b), g • Q.S'.rp b q = Q.S'.rp b q → law Q emb σ b g (P ⟨b, q⟩) = P ⟨b, q⟩ := by
    intro b q g hg
    apply cev_injective emb σ Q.sgT
    rw [cev_law emb σ hE h, hPz]
    exact (hz ⟨b, q⟩).2 ⟨g, hg⟩
  have key : ∀ b q (g : Q.S'.G b) (d : Q.S'.D b), g • Q.S'.rp b q = d →
      law Q emb σ b (Q.S'.mv b d) (P (Q.S'.cl b d)) = law Q emb σ b g (P ⟨b, q⟩) := by
    intro b q g d hd
    have hq : q = Quotient.mk (MulAction.orbitRel (Q.S'.G b) (Q.S'.D b)) d := by
      rw [← Q.S'.rp_spec b q]
      exact (Quotient.sound (⟨g, hd⟩ : (MulAction.orbitRel (Q.S'.G b) (Q.S'.D b)).r d (Q.S'.rp b q))).symm
    subst hq
    have h1 : Q.S'.mv b d • Q.S'.rp b (Quotient.mk _ d) = d := Q.S'.mv_smul b d
    have h2 := hfix b (Quotient.mk _ d) (g⁻¹ * Q.S'.mv b d) (by rw [mul_smul, h1, inv_smul_eq_iff, hd])
    refine Eq.trans ?_ (congrArg (law Q emb σ b g) h2)
    rw [← Module.End.mul_apply ((law Q emb σ b) g), ← map_mul, mul_inv_cancel_left]
  refine ⟨⟨fun b d => law Q emb σ b (Q.S'.mv b d) (P (Q.S'.cl b d)), fun b d => ⟨?_, fun g _ => ?_⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hP _))
  · have h1 : Q.S'.mv b d • Q.S'.rp b (Quotient.mk _ d) = d := Q.S'.mv_smul b d
    refine (key b (Quotient.mk _ d) (g * Q.S'.mv b d) (g • d) (by rw [mul_smul, h1])).trans ?_
    rw [map_mul]
    rfl
  · funext c
    have h1 := key c.1 c.2 1 (Q.S'.rep c) (one_smul _ _)
    rw [map_one] at h1
    exact (congrArg (cev emb σ Q.sgT) h1).trans (hPz c)

omit hE in
theorem petersson_apply (h : Q.Ok) (z w : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) :
    Q.ipP emb σ h z w = letI := Q.clFin h; ∑ c, Q.wt c * ipVal emb σ Q.sgT (z c) (w c) := by
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

omit hE in
theorem period_eq (hI : I.Ok) (h : Q.Ok) (hc : ι → HCParam R) (w : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (F : Q.Mt emb σ) :
    (Q.per emb σ hI h hc).period w F = Q.ipP emb σ h (jM Q emb σ F) w := by
  rw [petersson_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (ipVal_cev emb σ Q.sgT _ _).symm

omit hE in
theorem re_petersson_self_pos (h : Q.Ok) (z : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (hz : z ∈ Q.S'.Fi emb σ Q.sgT) (h0 : z ≠ 0) :
    0 < (Q.ipP emb σ h z z).re := by
  letI := Q.clFin h
  refine (Complex.lt_def.mp ?_ : (0 : ℂ).re < _ ∧ _).1
  rw [petersson_apply]
  have hw : ∀ c, 0 < Q.wt c := fun c => by
    haveI := h.step.fin_stab c.1 (Q.S'.rep c)
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨c, hc⟩ := Function.ne_iff.1 h0
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, mul_pos (hw c) (ipVal_pos emb σ _ (hz c).1 hc)⟩
  by_cases h1 : z c = 0
  · simp [h1]
  · exact (mul_pos (hw c) (ipVal_pos emb σ _ (hz c).1 h1)).le

end Per

open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem period_conj : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow, Function.Injective jM ∧ (∀ z ∈ (I.fm l u a).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (I.fm l u a).ptC) ∧ (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) ∧ ∀ z ∈ (I.fm l u a).ptC, z ≠ 0 → 0 < ((I.fm l u a).ipP z z).re := by
  intro B X I _ _ l _ u a
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  exact ⟨jM (I.perIn u a) B.fields.emb B.embLL, jM_injective _ _ hH, jM_onto _ _ hE (l.per u a),
    jM_mem _ _ hE (l.per u a) hH, period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u), re_petersson_self_pos _ _ (l.per u a)⟩

end GlobalTheory.Mem.Col2.PerConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversal
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CoefIrred

theorem vv_universal :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V] [Module ℂ V] (F : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) V), ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V, ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  intro ι _ n lam V _ _ F
  have hB : ∀ i, Formalism.L2.DIV.bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
    intro i
    apply Subtype.ext
    rw [Formalism.L2.DIV.bVV_coe, tenMul_coe, Formalism.L2.DIV.bVVfun]
    simp only [ssBasis_coe]
  refine ⟨(Formalism.L2.DIV.bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ))), ?_, ?_⟩
  · intro u
    have := Module.Basis.ext_multilinear (f := ((Formalism.L2.DIV.bVV ℂ lam).constr ℂ
      (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))).compMultilinearMap (tenMul lam)) (g := F)
      (fun τ => ssBasis ℂ (lam τ)) (fun v => by
        simp only [LinearMap.compMultilinearMap_apply, ← hB, Module.Basis.constr_basis])
    exact congrArg (fun m => m u) this
  · intro g hg
    apply (Formalism.L2.DIV.bVV ℂ lam).ext
    intro i
    rw [Module.Basis.constr_basis, hB, hg]

end GlobalTheory.CoefIrred
end

