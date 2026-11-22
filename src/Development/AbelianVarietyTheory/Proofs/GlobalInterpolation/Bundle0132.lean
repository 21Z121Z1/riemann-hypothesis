import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.KerExt

theorem exists_ext {G P T β X : Type} [Group G] [MulAction G P] [Group T] {H D : β → Type} [∀ b, Group (H b)]
    [∀ b, MulAction (H b) (D b)] (ρ : G → X → X) (ρ1 : ∀ x, ρ 1 x = x) (ρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (pt : ∀ b, D b → P) (hom : ∀ b, H b →* G) (zeta : T →* G)
    (pt_smul : ∀ b g d, pt b (g • d) = hom b g • pt b d)
    (gen : ∀ b (g : G), ∃ ζ g', g = zeta ζ * hom b g')
    (comm : ∀ ζ (g : G), zeta ζ * g = g * zeta ζ)
    (surj : ∀ p : P, ∃ ζ b d, p = zeta ζ • pt b d)
    (idx : ∀ ζ b b' d d', zeta ζ • pt b d = pt b' d' → b = b')
    (inj : ∀ ζ b d d', zeta ζ • pt b d = pt b d' → ∃ g : H b, g • d = d' ∧ ∀ x, ρ (hom b g) x = ρ (zeta ζ) x)
    (φ : ∀ b, D b → X) (hφ : ∀ b g d, φ b (g • d) = ρ (hom b g) (φ b d)) :
    ∃ Φ : P → X, (∀ b d, Φ (pt b d) = φ b d) ∧ ∀ g p, Φ (g • p) = ρ g (Φ p) := by
  have key : ∀ g ζ b d ζ' b' d', g • zeta ζ • pt b d = zeta ζ' • pt b' d' →
      ρ (zeta ζ') (φ b' d') = ρ g (ρ (zeta ζ) (φ b d)) := by
    intro g ζ b d ζ' b' d' h
    obtain ⟨ζ₀, g₀, rfl⟩ := gen b g
    have e : zeta (ζ'⁻¹ * ζ₀ * ζ) * hom b g₀ = (zeta ζ')⁻¹ * (zeta ζ₀ * hom b g₀ * zeta ζ) := by
      rw [map_mul, map_mul, map_inv, mul_assoc, comm ζ]
      simp only [mul_assoc]
    have h1 : zeta (ζ'⁻¹ * ζ₀ * ζ) • pt b (g₀ • d) = pt b' d' := by
      rw [pt_smul, ← mul_smul, e, mul_smul, mul_smul, h, inv_smul_smul]
    obtain rfl := idx _ _ _ _ _ h1
    obtain ⟨g₁, rfl, hg⟩ := inj _ _ _ _ h1
    rw [hφ, hg, hφ, ← ρm, ← ρm, ← ρm, mul_assoc, e, mul_inv_cancel_left]
  choose z i d hp using surj
  refine ⟨fun p => ρ (zeta (z p)) (φ (i p) (d p)), fun b x => ?_, fun g p => ?_⟩
  · have := key 1 1 b x (z (pt b x)) (i (pt b x)) (d (pt b x)) (by rw [← hp, map_one, one_smul, one_smul])
    exact this.trans (by rw [map_one, ρ1, ρ1])
  · exact key g (z p) (i p) (d p) _ _ _ (by rw [← hp, ← hp])

theorem exists_cplx {K V V' W W' : Type} [Field K] (σ : K →+* ℂ) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : V →ₛₗ[σ] W) (e' : V' →ₛₗ[σ] W')
    (li : LinearIndependent ℂ fun j => e (Module.Basis.ofVectorSpace K V j))
    (sp : Submodule.span ℂ (Set.range e) = ⊤) (f : V →ₗ[K] V') :
    ∃ fC : W →ₗ[ℂ] W', ∀ F, fC (e F) = e' (f F) := by
  set b := Module.Basis.ofVectorSpace K V
  have hmem : ∀ F, e F ∈ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have sp' : ⊤ ≤ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    rw [← sp, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact hmem F
  let c := Module.Basis.mk li sp'
  refine ⟨c.constr ℂ fun j => e' (f (b j)), fun F => ?_⟩
  have h : (c.constr ℂ fun j => e' (f (b j))).comp e = e'.comp f := by
    refine b.ext fun j => ?_
    have : e (b j) = c j := by simp [c]
    simp only [LinearMap.comp_apply, this, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h F

section Real

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

def evM : B.V i →ₛₗ[D.what₂.embLL] M.Val :=
  LinearMap.codRestrict M.Val (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL)
    fun F => by rw [R.val_eq]; exact evV_mem_ValC _ _ _ _ F

theorem evM_li : LinearIndependent ℂ fun j => evM R (Module.Basis.ofVectorSpace D.what₂.LL (B.V i) j) :=
  LinearIndependent.of_comp M.Val.subtype
    (evV_linearIndependent B.emb 1 (B.lam i) D.what₂.embLL (fr0 B.emb D.what₂.embLL _) _
      (Module.Basis.ofVectorSpace D.what₂.LL (B.V i)).linearIndependent)

theorem evM_span : Submodule.span ℂ (Set.range (evM R)) = ⊤ := by
  apply Submodule.map_injective_of_injective M.Val.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact (span_evV B.emb 1 (B.lam i) D.what₂.embLL).trans R.val_eq.symm

theorem evM_rho (b) (g : (B.I.S i).G b) (F : B.V i) :
    evM R ((B.I.S i).rho B.emb (B.lam i) b g F) = M.act (R.hom b g) (evM R F) := by
  apply Subtype.ext
  rw [R.act_hom]
  exact GStep.evV_rho_eq_tr _ _ _ _ b g F

theorem inj_act (ζ b d d') (h : R.zeta ζ • R.pt b d = R.pt b d') :
    ∃ g : (B.I.S i).G b, g • d = d' ∧ M.act (R.hom b g) = M.act (R.zeta ζ) := by
  obtain ⟨g, h1, h2, h3⟩ := (R.inj ζ b d d').1 h
  refine ⟨g, h3, LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [R.act_hom, R.act_zeta]
  funext x
  refine (trFr_apply B.emb D.what₂.embLL ((B.I.S i).gam b g) ((B.I.S i).chr b g) y.1 x).trans ?_
  rw [h1, h2, inv_one, frMul_one]
  rfl

theorem inj_act_inv (ζ b) (g : (B.I.S i).G b) (h : M.act (R.hom b g) = M.act (R.zeta ζ)) :
    M.act (R.hom b g)⁻¹ = M.act (R.zeta ζ)⁻¹ := by
  calc M.act (R.hom b g)⁻¹ = M.act (R.hom b g)⁻¹ * (M.act (R.zeta ζ) * M.act (R.zeta ζ)⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = _ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem ext_evM {W : Type} [AddCommGroup W] [Module ℂ W] {f g : M.Val →ₗ[ℂ] W} (h : ∀ F, f (evM R F) = g (evM R F)) :
    f = g :=
  LinearMap.ext_on_range (evM_span R) h

end Real

theorem exists_kerPt : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  intro D u B i sp sp' M M' R R' k hk
  choose kC hkC using fun b b' d d' =>
    exists_cplx D.what₂.embLL (evM R) (evM R') (evM_li R) (evM_span R) (k b b' d d')
  have hequiv : ∀ b b' (g : (B.I.S i).G b) (g' : (B.I.S (i + 1)).G b') d d',
      kC b b' (g • d) (g' • d') = M'.act (R'.hom b' g') ∘ₗ kC b b' d d' ∘ₗ M.act (R.hom b g)⁻¹ := by
    intro b b' g g' d d'
    refine ext_evM R fun F => ?_
    rw [hkC, hk.equiv, ← map_inv]
    simp only [LinearMap.comp_apply]
    rw [evM_rho, ← evM_rho R, hkC]

  have h1 : ∀ b d, ∃ Φ : M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b' d', Φ (R'.pt b' d') = kC b b' d d') ∧
      ∀ (g : M'.G) p, Φ (g • p) = M'.act g ∘ₗ Φ p := by
    intro b d
    refine exists_ext (fun (g : M'.G) (x : M.Val →ₗ[ℂ] M'.Val) => M'.act g ∘ₗ x) ?_ ?_ R'.pt R'.hom R'.zeta R'.pt_smul
      R'.gen R'.comm R'.surj (fun ζ b b' d d' h => R'.idx ζ b b' d d' (congrArg Prod.fst h)) ?_
      (fun b' d' => kC b b' d d') ?_
    · intro x
      simp only [map_one]
      rfl
    · intro g h x
      simp only [map_mul]
      rfl
    · intro ζ b' d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R' ζ b' d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [h2]⟩
    · intro b' g d'
      have := hequiv b b' 1 g d d'
      rw [one_smul, map_one, inv_one, map_one] at this
      exact this
  choose Φ hΦ hΦe using h1

  obtain ⟨Ψ, hΨ, hΨe⟩ : ∃ Ψ : M.Pt → M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b d, Ψ (R.pt b d) = Φ b d) ∧
      ∀ (g : M.G) p, Ψ (g • p) = fun p' => Ψ p p' ∘ₗ M.act g⁻¹ := by
    refine exists_ext (fun (g : M.G) (x : M'.Pt → (M.Val →ₗ[ℂ] M'.Val)) p' => x p' ∘ₗ M.act g⁻¹) ?_ ?_ R.pt R.hom R.zeta
      R.pt_smul R.gen R.comm R.surj (fun ζ b b' d d' h => R.idx ζ b b' d d' (congrArg Prod.fst h)) ?_ Φ ?_
    · intro x
      simp only [inv_one, map_one]
      rfl
    · intro g h x
      simp only [mul_inv_rev, map_mul]
      rfl
    · intro ζ b d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R ζ b d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [inj_act_inv R ζ b g h2]⟩
    · intro b g d
      funext p'
      obtain ⟨ζ, b', d', rfl⟩ := R'.surj p'
      have := hequiv b b' g 1 d d'
      rw [one_smul, map_one, map_one] at this
      simp only [hΦe, hΦ, this]
      rfl
  have hpt : ∀ b b' d d', Ψ (R.pt b d) (R'.pt b' d') = kC b b' d d' := fun b b' d d' => by rw [hΨ, hΦ]
  refine ⟨⟨Ψ, fun g p p' y => ?_, fun c c' y => ?_⟩, fun g' p p' y => ?_, fun b b' d d' F y hy => ?_⟩
  · rw [hΨe]
    show Ψ p p' ((M.act g⁻¹ * M.act g) y) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [R.rep_eq, R'.rep_eq, hpt]
    have : B.ch.C.Kmap i c c' ∘ₗ M.Val.subtype =
        M'.Val.subtype ∘ₗ kC c.1 c'.1 ((B.I.S i).rep c) ((B.I.S (i + 1)).rep c') := by
      refine ext_evM R fun F => ?_
      simp only [LinearMap.comp_apply]
      rw [hkC]
      exact hk.kmap c c' F
    exact LinearMap.congr_fun this y
  · obtain ⟨ζ, b, d, rfl⟩ := R.surj p
    show Ψ _ _ y = M'.act g' (Ψ _ _ y)
    simp only [hΨe, hΨ, hΦe]
    rfl
  · obtain rfl : y = evM R F := Subtype.ext hy
    show (Ψ _ _ _).1 = _
    rw [hpt, hkC]
    rfl

end GlobalTheory.LvT.Built.KerExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OffOfNotMem
section
noncomputable section

namespace GlobalTheory.LvT.Built.SplitPts

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem exists_ufGL {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : GL (Fin n) E)
    (h : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) : ∃ g : UF E n, ufGL E n g = γ := by
  obtain ⟨e, rfl⟩ := (toGLm E n).surjective γ
  refine ⟨⟨e, fun x y => ?_⟩, rfl⟩
  rw [← toGLm_mulVec e x, ← toGLm_mulVec e y]
  show star ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ x) ⬝ᵥ ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem sameOff_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    {N N' : Submodule (𝓞 E) (Sp E n)} (g : Sp E n ≃ₗ[E] Sp E n) (h : SameOff ST N N') :
    SameOff ST (gmap g N) (gmap g N') := fun w hw => by
  ext x
  rw [mem_localization_gmap, mem_localization_gmap, h w hw]

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

variable (sel) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (i : ℕ)

def offSetoid : Setoid (PtAt R sel mu cst u i) where
  r := SameOffPt sel mu cst u
  iseqv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
      fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
        h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_of_notMem (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (h : (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) :
    ∀ P ∈ Pr.vT u, w ≠ P ∧ w ≠ conjPrime₂ P := fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h

theorem ys_congr (hPr : Pr.Ok) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal)
    {N N' : Submodule (𝓞 X.E) (Sp X.E (R.N i))} (h : SameOff (Pr.vT u) N N') :
    (ysAt R sel mu cst i).ys N' = (ysAt R sel mu cst i).ys N := by
  classical
  have h1 : ∀ w : rowSG Pr sel mu, localization₂ w.1.asIdeal N' = localization₂ w.1.asIdeal N := fun w =>
    (h w.1 (off_of_notMem u hPr
      ((Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)))).symm
  unfold ysAt
  split_ifs
  · show ybSet sel mu cst N' = ybSet sel mu cst N
    simp only [ybSet, locLat, h1]
  · rfl

theorem exists_split : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)), ∃ sp : Split (tdatAt sel mu cst L Tp u i) (Pr.T u), ∀ b p q, (sp.off b).r p q ↔ SameOffPt sel mu cst u p q := by
  intro X Pr R _ Ch sel S mu cst L G m2 u i hX hPr hs hT _ Tp
  classical
  have hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal :=
    fun w hw => notMem_QE hs mu hw (hPr.T_prime u) hT
  have hM := moveHyp_of_ok hPr u
  have hQ' : ∀ (P : Pr.vT u) (w : QE sel (mu : Chr X.F X.E X.K)), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2)
  have hy := ysAt_off (R := R) sel mu cst hPr u hQ i
  refine ⟨{ off := fun _ => offSetoid sel mu cst u i
            off_act := ?_
            off_lat := fun _ _ _ h => h.1
            ext := ?_
            surj := ?_
            off_up := ?_
            off_dn := ?_
            off_dia := ?_
            dia_deco := ?_
            gam_surj := ?_
            T_mem := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1
            T_nsq := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2
            nonconj := fun P hP Q hQ => (hM ⟨P, hP⟩).st ⟨Q, hQ⟩ }, fun _ _ _ => Iff.rfl⟩
  · rintro b g p q ⟨h1, h2, h3, h4⟩
    refine ⟨sameOff_gmap g.1.1 h1, ?_, ?_, ?_⟩
    · funext w x
      show (g.2.1.1 w).1.mulVec (p.1.1.deco.1.be w (g.1.1.symm x)) = (g.2.1.1 w).1.mulVec (q.1.1.deco.1.be w (g.1.1.symm x))
      rw [h2]
    · funext w
      show g.1.1 * p.1.1.fr w * ((g.2.2.1 w)⁻¹).1 = g.1.1 * q.1.1.fr w * ((g.2.2.1 w)⁻¹).1
      rw [h3]
    · show (fun v => g.1.1 v) '' p.1.2 = (fun v => g.1.1 v) '' q.1.2
      rw [h4]
  · rintro b p q ⟨-, h2, h3, h4⟩ h
    have hN := congrArg Deco.N h
    have hf := congrArg Deco.f h
    exact PtY.ext' (Subtype.ext (Deco.ext hN hf h2)) h3 h4
  · intro b p e he h
    have hok := GlobalTheory.LvT.Pts.ok_of_agree p.1.1.deco.2 he
      fun w => h w.1 (off_of_notMem u hPr (T_notMem_vGs hPr u w))
    have hm := PtY.mv_spec p ⟨_, hok⟩ (fun w => (h w.1 (off_of_notMem u hPr (hQ w.1 w.2))).symm)
      (ys_congr sel mu cst u i hPr hQ h)
    have e1 := congrArg Subtype.val hm.1
    refine ⟨PtY.mv p ⟨_, hok⟩, ⟨?_, (congrArg Deco.be e1).symm, hm.2.1.symm, hm.2.2.symm⟩, ?_⟩
    · rw [e1]; exact h
    · have hN := congrArg Deco.N e1
      have hf := congrArg Deco.f e1
      exact Deco.ext hN hf (funext fun w => absurd w.2 (Finset.notMem_empty _))
  · intro b p P x hx hf
    have hm := mv_up (Pr.T u) p P (hM P) (T_unif hX hPr u P) (hQ' P) (hy P) hx hf
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((upN_spec p.1.1.deco.2.lat p.1.1.deco.2.uni P.1 (hM P).ne hx).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P g hg
    have e : (tdatAt sel mu cst L Tp u i).deco b p = p.1.1.deco.1.res (Finset.empty_subset _) :=
      Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))
    rw [e] at hg
    have hg' := dn_ok_of_res p.1.1.deco.2 P (hM P) (g := g) hg
    have hm := mv_dn p P (hM P) (hQ' P) (hy P) hg'
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((p.1.1.deco.2.dnN_spec P (hM P).ne).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P a
    show SameOffPt sel mu cst u p (PtY.mv p (DecoSet.dia1 P a p.1.1.deco))
    rw [PtY.mv_dia]
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  · intro b p P P' a hne
    show (PtY.mv p (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.f P' = p.1.1.deco.1.f P'
    rw [PtY.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG X.E (Pr.vT u)) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne hne, Units.val_one, one_mul]
  · intro b γ h
    obtain ⟨g, hg⟩ := exists_ufGL γ h
    exact ⟨(g, 1, 1), hg⟩

end GlobalTheory.LvT.Built.SplitPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdSubEqOrdDet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.DetIdlValue

variable {X : Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem finprod_group {M : Type} [CommMonoid M] (hX : X.Ok) (hsel : IsSel X sel) (g : HeightOneSpectrum (𝓞 X.E) → M)
    (hfin : (Function.mulSupport g).Finite) (h1 : ∀ w, conjPrime₂ w = w → g w = 1) :
    ∏ᶠ w, g w = ∏ᶠ v, g (sel v) * g (conjPrime₂ (sel v)) := by
  classical
  have hu : ∀ v, (sel v).under (𝓞 X.F) = v := fun v => HeightOneSpectrum.ext (hsel v)
  have hu' : ∀ v, (conjPrime₂ (sel v)).under (𝓞 X.F) = v := fun v =>
    HeightOneSpectrum.ext ((GlobalTheory.MuOffMove.under_conjP hX _).trans (hsel v))
  have hsub : Function.mulSupport (fun v => g (sel v) * g (conjPrime₂ (sel v))) ⊆
      (hfin.toFinset.image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_image]
    by_cases h : g (sel v) = 1
    · refine ⟨conjPrime₂ (sel v), hfin.mem_toFinset.2 fun h' => hv ?_, hu' v⟩
      simp only [h, h', mul_one]
    · exact ⟨sel v, hfin.mem_toFinset.2 h, hu v⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, finprod_eq_prod _ hfin,
    ← Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hc : conjPrime₂ (sel v) = sel v
  · rw [hc, h1 _ hc, mul_one]
    refine Finset.prod_eq_one fun w hw => h1 w ?_
    by_contra hw'
    have hwv : w.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2
    rcases ((GlobalTheory.ThetaMove.split_of_conj_ne₂ X w v hX hw' hwv).2 (sel v)).1 (hsel v) with e | e
    · exact hw' (e ▸ hc)
    · rw [e, GlobalTheory.CharValCompare.conjP_conjP] at hc
      exact hw' hc.symm
  · have hsp := (GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)).2
    rw [← Finset.prod_pair (Ne.symm hc)]
    refine Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact (hsp w).1 (congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2)
    · by_contra hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      exact hw' (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hg, HeightOneSpectrum.ext ((hsp w).2 hw)⟩)

theorem pow_toNat_mul {G : Type} [CommGroup G] (a : G) (k : ℤ) : a ^ k.toNat * a⁻¹ ^ (-k).toNat = a ^ k := by
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_sub, Int.toNat_sub_toNat_neg]

theorem ordSub_eq_ordDet {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ordSub w (GlobalTheory.Mem.Chr.detSub N) = ordDet w N :=
  ordSub_detSub_eq hN (GlobalTheory.CharValCompare.isFr_frameAt (GlobalTheory.CharValCompare.exists_isFr w hN))

theorem inv_val_detIdl : ∀ (X : Fields) (n : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (χ : Formalism.L2.Host.HChar X.E) (σ : X.K →+* ℂ) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : HeightOneSpectrum (𝓞 X.E) → Sp X.E n ≃ₗ[X.E] Sp X.E n), X.Ok → IsSel X sel → IsSdLat N → χ.TrivOn X.F → (∀ w, w ∉ SB → conjPrime₂ w ∉ SB → χ.UnrAt w ∧ σ ((mU w : X.Kˣ) : X.K) = ((χ.val w : ℂˣ) : ℂ)⁻¹) → ((χ.1 (detIdl SB N fr) : ℂˣ) : ℂ)⁻¹ = σ (muOff sel SB mU N) * ∏ P : SB, ((χ.locK P.1 (LinearEquiv.det (fr P.1)) : ℂˣ) : ℂ)⁻¹ := by
  intro X n sel SB χ σ mU N fr hX hsel hN hT hU
  classical
  set g : HeightOneSpectrum (𝓞 X.E) → ℂˣ := fun w =>
    if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else χ.val w ^ (ordDet w N).toNat with hg
  have hfin : (Function.mulSupport g).Finite := by
    refine (GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.subset fun w hw h0 => hw ?_
    simp [hg, h0]
  have h0 : ∀ w, conjPrime₂ w = w → ordDet w N = 0 := fun w hw => by
    have := GlobalTheory.OrdDetConj.ordDet_conjP hN w
    rw [hw] at this
    omega
  have h1 : ∀ w, conjPrime₂ w = w → g w = 1 := fun w hw => by simp [hg, h0 w hw]
  have e1 : χ.1 (detIdl SB N fr) = (∏ P ∈ SB, χ.locK P (LinearEquiv.det (fr P))) * ∏ᶠ w, g w := by
    unfold detIdl
    rw [map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN.1)]
    congr 1
    refine finprod_congr fun w => ?_
    simp only [hg]
    split_ifs
    · exact map_one _
    · rw [map_pow, ordSub_eq_ordDet hN.1]
      rfl
  have e2 : ∀ v, σ (GlobalTheory.MuOffMove.term sel SB mU N v) = (((g (sel v) * g (conjPrime₂ (sel v)))⁻¹ : ℂˣ) : ℂ) := by
    intro v
    unfold GlobalTheory.MuOffMove.term
    by_cases hc : conjPrime₂ (sel v) = sel v
    · rw [hc, h1 _ hc, h0 _ hc]
      simp
    · obtain ⟨hm, hsp⟩ := GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)
      by_cases hv : sel v ∈ SB ∨ conjPrime₂ (sel v) ∈ SB
      · have hv' : ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal :=
          hv.elim (fun h => ⟨_, h, (hsp _).2 (Or.inl rfl)⟩) fun h => ⟨_, h, (hsp _).2 (Or.inr rfl)⟩
        rw [if_pos hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_pos hv, if_pos hv.symm]
        simp
      · have hv' : ¬ ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
          rintro ⟨P, hP, e⟩
          rcases (hsp P).1 e with rfl | rfl
          exacts [hv (Or.inl hP), hv (Or.inr hP)]
        obtain ⟨ha, hb⟩ := not_or.1 hv
        obtain ⟨u1, s1⟩ := hU _ ha hb
        obtain ⟨u2, -⟩ := hU _ hb (by rwa [GlobalTheory.CharValCompare.conjP_conjP])
        rw [if_neg hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_neg hv, if_neg fun h => hv (Or.symm h), GlobalTheory.OrdDetConj.ordDet_conjP hN,
          GlobalTheory.HeckeSplit.val_eq_inv_of_split X.F X.E χ v _ _ hT u1 u2 (Ne.symm hc) hm, pow_toNat_mul,
          Units.val_zpow_eq_zpow_val, map_zpow₀, s1, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, inv_zpow]
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  have e3 : σ (muOff sel SB mU N) = (((∏ᶠ w, g w)⁻¹ : ℂˣ) : ℂ) := by
    change σ (∏ᶠ v, GlobalTheory.MuOffMove.term sel SB mU N v) = _
    rw [finprod_group hX hsel g hfin h1, ← finprod_inv_distrib,
      map_finprod σ (GlobalTheory.MuOffMove.term_finite hsel SB mU hN), finprod_congr e2]
    exact ((Units.coeHom ℂ).map_finprod_of_injective Units.val_injective
      fun v => (g (sel v) * g (conjPrime₂ (sel v)))⁻¹).symm
  rw [e3, e1, Finset.prod_coe_sort SB fun P => ((χ.locK P (LinearEquiv.det (fr P)) : ℂˣ) : ℂ)⁻¹]
  simp [mul_comm]

end GlobalTheory.DetIdlValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatStepOfChThOk
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.KerT

theorem ratStep_of_chTh_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i < R.m → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A _ _ _ _ _ _ hL _ hT hi
  have hq := Formalism.L2.Ker.muqTie_of_ok Ch sel mu cst L hL
  have hm := hL.hm
  have key : ∀ j, (j = i + 1 ∧ i ≤ m2) ∨ (j = R.m ∧ i = m2 + 1) → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i j := by
    intro j hj
    unfold RatStep
    rw [← Formalism.L2.Ker.stepC_eq_stepT W Ch sel mu cst hq A u i hi]
    rcases hj with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · intro γ γ' N fr N' fr' c x h'
      exact (hT.th i h).equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
    · intro γ γ' N fr N' fr' c x h'
      exact hT.top.equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
  exact key _ (by omega)

end GlobalTheory.KerT
end

