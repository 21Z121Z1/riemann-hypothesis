import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def FramedX {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) {J : Type} (t : J → (UA E a →₀ ℂ)) : Prop :=
  ∃ (X : Type) (b : UA E a → X → W.Sp), (∀ f : algForms W, ∃ R : ℝ, ∀ g i, ‖ι.symm (f.1 (b g i) g)‖ ≤ R) ∧
    (∀ f : algForms W, (∀ g i, f.1 (b g i) g = 0) → f = 0) ∧
    ∀ (F : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R : ℝ), (∀ g i, ‖ι.symm (F (b g i) g)‖ ≤ R) →
      ∀ j g i, ‖ι.symm (opOf (RU E a) (t j) (F (b g i)) g)‖ ≤ R

theorem Framed.framedX {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {W : Wt E a} {J : Type} {t : J → (UA E a →₀ ℂ)}
    (h : Framed ι W t) : FramedX ι W t := by
  obtain ⟨d, b, h⟩ := h
  exact ⟨Fin d, b, h⟩

def DenomLe (l d : ℕ) (g : UA E a) : Prop :=
  ∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
    IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
    IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (u.adicCompletion E)))

def IntW {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ ∃ d : ℕ, DenomLe l d g ∧ ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

theorem intW_of {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {lam : (E →+* ℂ) → DomWeight a} {w₀ : HeightOneSpectrum (𝓞 E)}
    {f : UA E a →₀ ℂ} (h : IsIntegralOpW ι lam w₀ f) : IntW ι lam f :=
  fun g hg => ⟨(h g hg).1, (h g hg).2.2⟩

def CoefLe {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type} (R : ℝ) (x : MvPolynomial σ ℂ) : Prop :=
  ∀ m, ‖ι.symm (MvPolynomial.coeff m x)‖ ≤ R

def ToPolyX : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)), K ≤ finU E a → ∀ (lam : (E →+* ℂ) → DomWeight a)
    (P : Submodule ℂ (UA E a → ℂ) → Prop), Dense ι (Wt.ofFam lam) K P → ∀ (J : Type) (t : J → (UA E a →₀ ℂ))
    (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), FramedX ι (Wt.ofFam lam) t → ActsBy K t η → ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η U' j)}

def Kappa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    ∃ κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ), (∀ γ ∈ ratU E n, κ γ = cAll γ) ∧ (∀ x ∈ infU E n, κ x = 1) ∧
      ∀ (g : UA E n) (d : ℕ), DenomLe l d g → ∀ v i j,
        ‖ι.symm (((κ g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d ∧
        ‖ι.symm ((((κ g v)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d

def DenomBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ (n : ℕ) (Z : Set (UA E n)), IsCompact Z →
    ∃ d : ℕ, ∀ g ∈ Z, DenomLe l d g

def DegLe : Prop :=
  ∀ (T : Type) [Fintype T] (n : ℕ) (lam : T → DomWeight n), ∀ x ∈ Formalism.L2.DIV.VV ℂ lam,
    x.totalDegree ≤ ∑ τ, ∑ i, (lam τ).natW i

def BlockBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (T : Type) (n : ℕ) (A : T → Matrix (Fin n) (Fin n) ℂ) (R : ℝ), 1 ≤ R →
    (∀ τ i j, ‖ι.symm (A τ i j)‖ ≤ R) → ∀ (D : ℕ) (x : MvPolynomial (T × Fin n × Fin n) ℂ), x.totalDegree ≤ D → CoefLe ι 1 x →
    CoefLe ι (R ^ D) (Formalism.GradedWeylDivisibility.blockAct ℂ A x)

def DetBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (T : Type) [Fintype T] (n : ℕ) (lam : T → DomWeight n) (A : T → GL (Fin n) ℂ) (R : ℝ),
    1 ≤ R → (∀ τ i j, ‖ι.symm (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ R ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ R) →
    ‖ι.symm (Formalism.L2.DIV.detTwK lam A)‖ ≤ R ^ (∑ τ, n * (lam τ).detShift.natAbs)

def SizeLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a),
    (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs ≤ a * wtSize W.at

def RhoBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a)
    (A : InfinitePlace E → GL (Fin a) ℂ) (R : ℝ), 1 ≤ R →
    (∀ τ i j, ‖ι.symm (((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ R ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ R) →
    ∀ x : W.Sp, CoefLe ι 1 x.1 → CoefLe ι (R ^ (a * wtSize W.at)) (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1

def LatFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (σ : Type) (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V],
    (∀ φ : V →ₗ[ℂ] ℂ, ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) (x : V), CoefLe ι R x.1 → ‖ι.symm (φ x)‖ ≤ M * R) ∧
    ∀ x : V, ∃ c : ℂ, c ≠ 0 ∧ CoefLe ι 1 (c • x).1

def LevelEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (f : algForms W),
    ∃ C : Subgroup (UA E a), IsLevel C ∧ f ∈ fixedBy W C

def FrameW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a) (J : Type)
    (t : J → (UA E a →₀ ℂ)), (∀ j, IntW ι W.at (t j)) → FramedX ι W t

def ScaleW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ), (∀ g ∈ f.support, g ∈ finU E a) → ∃ c : ℂ, c ≠ 0 ∧ IntW ι lam (c • f)

def HypOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (K : Subgroup (UA E a)), IsCompact (K : Set (UA E a)) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → x ∈ K) → HypAt K w

def MaxCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (H : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (Z : Set (GL (Fin a) (w.adicCompletion E))), IsCompact Z → (H : Set (GL (Fin a) (w.adicCompletion E))) ⊆ Z →
    GlobalTheory.LFun.KGL w a ≤ H → H ≤ GlobalTheory.LFun.KGL w a

def PowNhds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a N : ℕ), N ≠ 0 →
    ∀ V ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), (fun x => x ^ N) '' V ∈ nhds (1 : GL (Fin a) (w.adicCompletion E))

def KerOpen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (J : Subgroup (GL (Fin a) (w.adicCompletion E))),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (A : Type) [Group A] [Finite A] (θ : J →* A),
    ∃ N : Set (GL (Fin a) (w.adicCompletion E)), IsOpen N ∧ 1 ∈ N ∧ ∀ x : J, x.1 ∈ N → θ x = 1

def TyStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ → ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (W : Wt E a)
    (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), ∀ f ∈ fixedBy W (lev K w₀ J),
      ∃ G ∈ part W K (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U),
        ∃ e : UA E a → ℂ, (∀ g, ‖ι.symm (e g)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ m) ∧ ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g

def TwistPart : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a))
    (W : Wt E a) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (A : Type) [Group A] (θ : J →* A) (χ : A →* ℂˣ)
    (hC : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J), (∀ k ∈ K, cLoc w₀ k = 1) → ∀ F : algForms W,
    (∀ c (hc : c ∈ lev K w₀ J) v g, F.1 v (g * c) = ((χ (θ ⟨cLoc w₀ c, hC c hc⟩) : ℂˣ) : ℂ) * F.1 v g) →
    F ∈ part W K fun U => HasTypeVec w₀ K J θ χ U

def CharSum : Prop :=
  ∀ (N : ℕ) [NeZero N], ∃ (s : Finset (Multiplicative (ZMod N) →* ℂˣ)), (∀ χ ∈ s, χ ≠ 1) ∧
    ∀ x : Multiplicative (ZMod N), 1 + ∑ χ ∈ s, ((χ x : ℂˣ) : ℂ) = 0 ∨ 1 + ∑ χ ∈ s, ((χ x : ℂˣ) : ℂ) = N

def GenW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ), GenData w₀ K S Φ →
    ∀ P : Submodule ℂ (UA E a → ℂ) → Prop, Dense ι (Wt.ofFam lam) K P →
    ∀ (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), (∀ j, IntW ι lam (t j)) →
      ActsBy K t η → ∀ U, OfType lam K U →
        PolyApprox (fun j => ι.symm (η U j))
          {θ | ∃ U', OfType lam K U' ∧ P U' ∧ (∀ w ∈ S, GenAt w (Φ w) U') ∧ θ = fun j => ι.symm (η U' j)}

def DiscEx : Prop :=
  ∀ a : ℕ, ∃ D : MvPolynomial (Fin a) ℤ, D.IsSymmetric ∧ D.IsHomogeneous D.totalDegree ∧ D ≠ 0 ∧
    ∀ (k : Type) [Field k] (z : Fin a → k), MvPolynomial.aeval z D ≠ 0 → Function.Injective z ∧
      ∀ m : Fin a → ℕ, ∑ i, m i = a → ∏ i, z i ^ m i = ∏ i, z i → m = fun _ => 1

def DiscEx2 : Prop :=
  ∀ a n : ℕ, ∃ D : MvPolynomial (Fin a) ℤ, D.IsSymmetric ∧ D.IsHomogeneous D.totalDegree ∧ D ≠ 0 ∧
    ∀ (k : Type) [Field k] (z : Fin a → k), MvPolynomial.aeval z D ≠ 0 →
      (∀ i j, i ≠ j → ∀ c, 1 ≤ c → c ≤ n → z i ^ c ≠ z j ^ c) ∧ (∀ i j k', ¬ (i = j ∧ k' = j) → z i * z k' ≠ z j ^ 2)

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllPf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ell_pf :
    UpperTheory.Gal.Gen.EllGrp → UpperTheory.Gal.Gen.Ell := by
  intro hGrp E _ _ _ n C hLev H _ lam hU2 hfin
  have hC := hLev.fin
  have hCc := hLev.compact
  obtain ⟨U1, hU1o, hU11, hU1C⟩ := hLev.isOpen
  obtain ⟨U2, hU2o, hU21, hU2l⟩ := hU2
  set D : Subgroup (UA E n) := C ⊔ infU E n with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  let lam' : D →* H := lam.comp f
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E n
  have hI : IsCompact (infU E n : Set (UA E n)) := isCompact_iff_compactSpace.2 inferInstance
  have hDc : IsCompact (D : Set (UA E n)) := by
    rw [hDdef, Subgroup.mul_normal]
    exact hCc.mul hI
  have hyp : ∀ g : UA E n, ∀ γ ∈ ratU E n, ∀ d : D, γ * g = g * d → lam' d = 1 := by
    intro g γ hγ d h
    have hγ' : g * (d : UA E n) * g⁻¹ ∈ ratU E n := by
      rw [← h, mul_inv_cancel_right]; exact hγ
    have hd : IsOfFinOrder (d : UA E n) := GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints E n D hDc g d d.2 hγ'
    obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hd
    have hdm : d ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
    exact hfin (f d) (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, by rw [← map_pow, hdm, map_one]⟩)
  obtain ⟨ℓ, h1, h2⟩ := hGrp (UA E n) H (ratU E n) D lam' hyp
  have hinf : ∀ g, ∀ x ∈ infU E n, ℓ (g * x) = ℓ g := by
    intro g x hx
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [lam', MonoidHom.comp_apply, e, map_one, mul_one] at this
    exact this
  have hC' : ∀ g (c : C), ℓ (g * c) = ℓ g * lam c := by
    intro g c
    have e : f ⟨c, le_sup_left (b := infU E n) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E n) c.2⟩
    simp only [lam', MonoidHom.comp_apply, e] at this
    exact this
  set Wn : Set (UA E n) := GlobalTheory.EllU.finPart ⁻¹' (U1 ∩ U2) with hWn
  have hWo : IsOpen Wn := (hU1o.inter hU2o).preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E n) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ U1 ∩ U2
    rw [map_one]; exact ⟨hU11, hU21⟩
  have hWinv : ∀ g, ∀ w ∈ Wn, ℓ (g * w) = ℓ g := by
    intro g w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hU1C ⟨hw1, GlobalTheory.EllU.finPart_mem w⟩
    have hl : lam ⟨GlobalTheory.EllU.finPart w, hkC⟩ = 1 := hU2l ⟨GlobalTheory.EllU.finPart w, hkC⟩ hw2
    have e : g * w = g * GlobalTheory.EllU.finPart w * ((GlobalTheory.EllU.finPart w)⁻¹ * w) := by group
    rw [e, hinf _ _ (GlobalTheory.EllU.inv_finPart_mul_mem w)]
    have := hC' g ⟨GlobalTheory.EllU.finPart w, hkC⟩
    rw [hl, mul_one] at this
    exact this
  refine ⟨ℓ, hinf, hC', fun φ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    refine (continuousAt_const (y := φ (ℓ g))).congr ?_
    have hc : Continuous fun y : UA E n => g⁻¹ * y := continuous_const.mul continuous_id
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    change φ (ℓ g) = φ (ℓ y)
    have := hWinv g _ hy
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    change φ (ℓ (γ * g)) = φ (ℓ g)
    rw [h1 γ hγ g]
  · let S : Subgroup (finU E n) :=
      { carrier := {k | RU E n k (fun g => φ (ℓ g)) = fun g => φ (ℓ g)}
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [map_mul, Module.End.mul_apply]
          change RU E n a (RU E n b _) = _
          rw [hb, ha]
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n a _) = _
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    change IsOpen (S : Set (finU E n))
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    have ho : IsOpen ((Subtype.val : finU E n → UA E n) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hWinv g _ hk]
  · refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton (fun g => φ (ℓ g))).subset ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hinf g k k.2]
end

