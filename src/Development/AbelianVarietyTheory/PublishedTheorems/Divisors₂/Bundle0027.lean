import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

section Values

variable {n : ℕ}

def hermMat (α : Alt n) : Matrix (Fin n) (Fin n) ℂ :=
  of fun a b => -Complex.I * (bas n).repr α {a.castAdd n, b.natAdd n}

def eval₂ (α : Alt n) (ξ η : V n) : ℂ :=
  Complex.I * (HermFrame.form (hermMat α) ξ η - HermFrame.form (hermMat α) η ξ)

theorem bas_pair (a b : Fin n) : bas n {a.castAdd n, b.natAdd n} = dz a * dzb b := by
  have hlt : a.castAdd n < b.natAdd n := by
    rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
  have hc : ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))).card = 2 := Finset.card_pair hlt.ne
  have e : ⇑(({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))).orderEmbOfFin hc) = ![a.castAdd n, b.natAdd n] :=
    (Finset.orderEmbOfFin_unique hc (fun i => by fin_cases i <;> simp)
      (Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simpa using hlt)).symm
  rw [bas, ExteriorAlgebra.basis_apply_ofCard _ hc, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv, Set.powersetCard.ofCard, e, dz, dzb, -Fin.natAdd_eq_addNat]

theorem hermMat_sym (a b : Fin n) : hermMat (Complex.I • (dz a * dzb b)) a b = 1 := by
  simp [hermMat, ← bas_pair, ← mul_assoc]

end Values

def chPart (r j : ℕ) : symmetricSubalgebra (Fin r) ℚ := ((j.factorial : ℚ)⁻¹) • ⟨psum (Fin r) ℚ j, psum_isSymmetric _ _ j⟩

def tdPart (r j : ℕ) : symmetricSubalgebra (Fin r) ℚ :=
  ⟨homogeneousComponent j (∏ i, ∑ m ∈ Finset.range (j + 1), C (bernoulli' m / m.factorial) * X i ^ m), fun e => by
    rw [rename_homogeneousComponent, map_prod]
    congr 1
    exact Fintype.prod_equiv e _ _ fun i => by simp⟩

def rCoeff (m : ℕ) : ℝ := (2 * deriv riemannZeta (-m) + riemannZeta (-m) * (harmonic m : ℚ)).re

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

namespace ArRing

variable {B : BottChern} {h : IsRegVar p D} (R : ArRing B h) {r : ℕ} (E : HermVB p r)

def char : symmetricSubalgebra (Fin r) ℚ →ₐ[ℚ] R.CH :=
  (aeval fun i : Fin r => R.cl E (i + 1)).comp (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r)).symm.toAlgHom

def ch : R.CH := ∑ j ∈ Finset.range (D + 2), R.char E (chPart r j)

def td : R.CH := ∑ j ∈ Finset.range (D + 2), R.char E (tdPart r j)

def rForm : h.Fld :=
  ∑ m ∈ (Finset.range (D + 1)).filter Odd, (rCoeff m : ℂ) • h.coeFld (R.om (R.char E (chPart r m)))

theorem char_esymm (j : ℕ) : R.char E ⟨esymm (Fin r) ℚ j, esymm_isSymmetric _ _ j⟩ = R.cl E j := by
  rcases j with _ | j
  · rw [R.cl_zero, ← map_one (R.char E)]
    exact congrArg _ (Subtype.ext (esymm_zero (Fin r) ℚ))
  by_cases hj : j < r
  · exact (congrArg _ (esymmAlgEquiv_symm_apply ℚ (Fintype.card_fin r) ⟨j, hj⟩)).trans (aeval_X _ _)
  · rw [R.cl_eq_zero E _ (by omega), ← map_zero (R.char E)]
    refine congrArg _ (Subtype.ext ?_)
    simp only [esymm, ZeroMemClass.coe_zero]
    rw [Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty]

theorem char_chPart_zero : R.char E (chPart r 0) = r := by
  rw [← map_natCast (R.char E)]
  exact congrArg _ (Subtype.ext (by simp [chPart, psum_zero]))

theorem char_chPart_one : R.char E (chPart r 1) = R.cl E 1 := by
  rw [← char_esymm]
  exact congrArg _ (Subtype.ext (by simp [chPart, psum_one, esymm_one]))

theorem char_tdPart_zero : R.char E (tdPart r 0) = 1 := by
  rw [← map_one (R.char E)]
  exact congrArg _ (Subtype.ext (by simp [tdPart]))

theorem IsPull.char {h' : IsRegVar q D'} {R' : ArRing B h'} {π : Y ⟶ X} {hπ : π ≫ p = q} {f : R.CH →ₐ[ℚ] R'.CH}
    (H : R.IsPull R' π hπ f) (φ : symmetricSubalgebra (Fin r) ℚ) : f (R.char E φ) = R'.char (E.pull π hπ) φ := by
  simp only [ArRing.char, AlgHom.comp_apply, ← H.cl]
  exact comp_aeval_apply _ f _

end ArRing

variable (q) in

def IsGenSmooth (π : Y ⟶ X) : Prop :=
  ∃ U : Y.Opens, (∀ σ (y : CxPts q σ), y ∈ ptsIn q σ U) ∧ Smooth (U.ι ≫ π)

theorem IsGenSmooth.of_smooth (π : Y ⟶ X) [Smooth π] : IsGenSmooth q π :=
  ⟨⊤, fun _ _ => mem_ptsIn_top, inferInstance⟩

def IsRegVar.IsFibreInt (h : IsRegVar p D) (h' : IsRegVar q D') (π : Y ⟶ X) (hπ : π ≫ p = q) (η : h'.Fld) (η' : h.Fld) :
    Prop :=
  ∀ σ j φ, (h.atlas σ).IsRealForm j φ → (h.atlas σ).integral (η' σ * φ) =
    (h'.atlas σ).integral (η σ * (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map π hπ _) φ)

structure ArChow.Push {B : BottChern} (C : ArChow B k) where

  gr_zero : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D), ∀ x ∈ (C.ring h).gr 0,
    ∃ c : ℚ, x = algebraMap ℚ _ c

  push : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X), π ≫ p = q → IsGenSmooth q π → ((C.ring h').CH →ₗ[ℚ] (C.ring h).CH)

  mem : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i j : ℕ), i + D = j + D' → ∀ x ∈ (C.ring h').gr i,
    push h h' π hπ hs x ∈ (C.ring h).gr j

  eq_zero : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i : ℕ), i + D < D' → ∀ x ∈ (C.ring h').gr i,
    push h h' π hπ hs x = 0

  proj : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (x : (C.ring h).CH) (y : (C.ring h').CH),
    push h h' π hπ hs (C.pull h h' π hπ x * y) = x * push h h' π hπ hs y

  om : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (y : (C.ring h').CH),
    h.IsFibreInt h' π hπ (h'.coeFld ((C.ring h').om y)) (h.coeFld ((C.ring h).om (push h h' π hπ hs y)))

  a : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i j : ℕ), i + D = j + D' → ∀ η, h'.IsArForm i η →
    ∃ η', h.IsArForm j η' ∧ h.IsFibreInt h' π hπ η η' ∧ push h h' π hπ hs ((C.ring h').a η) = (C.ring h).a η'

  deg : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (y : (C.ring h').CH),
    (C.ring h).deg (push h h' π hπ hs y) = (C.ring h').deg y

  push_id : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D),
    push h h (𝟙 X) (Category.id_comp p) (.of_smooth _) = LinearMap.id

  push_comp : ∀ {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k} {D D' D'' : ℕ} (h : IsRegVar p D)
    (h' : IsRegVar q D') (h'' : IsRegVar t D'') (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (ρ : Z ⟶ Y)
    (hρ : ρ ≫ q = t) (hs' : IsGenSmooth t ρ) (hs'' : IsGenSmooth t (ρ ≫ π)),
    push h h'' (ρ ≫ π) (by rw [Category.assoc, hπ, hρ]) hs'' = push h h' π hπ hs ∘ₗ push h' h'' ρ hρ hs'

open Limits

def relCot (π : Y ⟶ X) : Y.Modules := Conormal.conormal (pullback.diagonal π)

def dRel (π : Y ⟶ X) (W : Y.Opens) (f : Γ(Y, W)) : Γ(relCot π, W) :=
  Conormal.d (pullback.diagonal_fst π) (V := W) (W := pullback.snd π π ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, pullback.diagonal_snd]; exact le_rfl) ((pullback.snd π π).app W f)

theorem isVB_relCot (π : Y ⟶ X) [QuasiSeparated π] (g : ℕ) [H : SmoothOfRelativeDimension g π] : IsVB (relCot π) g :=
  have : SmoothOfRelativeDimension g (pullback.fst π π) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback π π).flip H
  Conormal.isVB_conormal (pullback.diagonal_fst π) g

variable (q) in

def IsRelAcyclic (π : Y ⟶ X) (L : LB Y) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (W : κ → Y.Opens),
    (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = π ⁻¹ᵁ U → ∀ n, (AbLaw.cechLB q L W).ExactAt (n + 1)

example (L : LB Y) (W : Fin 1 → Y.Opens) (n : ℕ) : (AbLaw.cechLB q L W).ExactAt (n + 1) :=
  .of_isZero (AbLaw.isZero_cechLB_X q L W (by simp))

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InfiniteOfConcl
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisResLineModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_reps (x : Matrix (Fin n) (Fin 1) E) : ∃ T : Set (ratPts σ J), ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧
    ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  let P : Subgroup (ratPts σ J) :=
    { carrier := {p | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p.1).1 * adMat F x = l.1 • adMat F x}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro p q ⟨l, hp⟩ ⟨m, hq⟩
        refine ⟨l * m, ?_⟩
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul,
          Units.val_mul, mul_comm]
      inv_mem' := by
        rintro p ⟨l, hp⟩
        refine ⟨l⁻¹, ?_⟩
        have := congrArg (fun z => l⁻¹.1 • ((matHom _ σ J p.1⁻¹).1 * z)) hp
        simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mul, Matrix.mul_smul, smul_smul] at this
        simpa using this.symm }
  refine ⟨Set.range (fun q : Quotient (QuotientGroup.rightRel P) => q.out), fun γ => ?_⟩
  refine ⟨(Quotient.mk (QuotientGroup.rightRel P) γ).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · exact QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel P) γ)
  · rintro _ ⟨⟨q, rfl⟩, hq⟩
    have : Quotient.mk (QuotientGroup.rightRel P) q.out = Quotient.mk _ γ :=
      Quotient.sound (QuotientGroup.rightRel_apply.2 hq)
    rw [← this, Quotient.out_eq]

theorem hyps_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (x : Matrix (Fin 2) (Fin 1) E)
    (L : Submodule (𝓞 E) (Fin 2 → E)) (a : GL (Fin 2) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (T : Set (ratPts σ J)),
    IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧ IsWittFrame σ J X Y ∧
      x = X.submatrix id (fun _ => 0) ∧ IsAdapted σ J X Y L a ∧
      (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) ∧
      (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) ∧
      ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, L, a, hc, hu, hJ, hW, hA⟩ := GlobalTheory.EisLineModel.data_inhabited
  obtain ⟨h1, h, h2⟩ := GlobalTheory.IwLine.iwasawa_line F E σ hc hu 2 J hJ 0 X Y hW _ rfl L a hA
  obtain ⟨T, hT⟩ := exists_reps (σ := σ) (J := J) (X.submatrix id (fun _ : Fin 1 => 0))
  exact ⟨F, E, _, _, _, _, _, σ, J, X, Y, _, L, a, h, T, hc, hu, hJ, hW, rfl, hA, h1, h2, hT⟩

theorem neBot (n : ℕ) : (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Complex.closure_setOf_lt_re]
  have : ((n : ℂ) - 1) / 2 = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]; simp only [Set.mem_setOf_eq, Complex.ofReal_re, le_refl]

theorem infinite_of_concl {ι : Type} (n : ℕ) (c : ι → ℝ) (hc : ∀ i, 0 < c i) {R : ℂ} (hR : R ≠ 0)
    (h : Tendsto (fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : ι, (c t : ℂ) ^ (s + ((n : ℂ) - 1) / 2))
      (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)) (𝓝 R)) : Infinite ι := by
  by_contra hi
  haveI : Finite ι := not_infinite_iff_finite.1 hi
  haveI := Fintype.ofFinite ι
  haveI := neBot n
  have hcont : Continuous fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : ι, (c t : ℂ) ^ (s + ((n : ℂ) - 1) / 2) := by
    simp only [tsum_fintype]
    refine (continuous_id.sub continuous_const).mul (continuous_finset_sum _ fun t _ => ?_)
    exact (continuous_id.add continuous_const).const_cpow (Or.inl (by exact_mod_cast (hc t).ne'))
  have h2 := (hcont.tendsto (((n : ℂ) - 1) / 2)).mono_left
    (nhdsWithin_le_nhds (s := {s : ℂ | ((n : ℝ) - 1) / 2 < s.re}))
  have := tendsto_nhds_unique h h2
  simp at this
  exact hR this

theorem eisensteinIsotropicLine_of_isWittFrame (hP : GlobalTheory.Published.EisensteinResidueLine) : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E)
    (_ : NumberField E) (_ : Algebra F E) (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Matrix (Fin 2) (Fin 1) E)
    (T : Set (ratPts σ J)), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) ∧ Infinite T := by
  obtain ⟨F, E, _, _, _, _, _, σ, J, X, Y, x, L, a, h, T, hc, hu, hJ, hW, hx, hA, h1, h2, hT⟩ := hyps_inhabited
  obtain ⟨R, hR, hl⟩ := hP F E σ hc hu 2 J hJ 0 X Y hW x hx L a hA h h1 h2 T hT
  exact ⟨F, E, _, _, _, inferInstance, _, σ, J, x, T, hT,
    infinite_of_concl 2 (fun t : T => h (t.1.1 * 1)) (fun _ => (GlobalTheory.EisLineModel.pos h1 h2).1 _) hR (hl 1)⟩

end GlobalTheory.EisResLineModel

end
end

