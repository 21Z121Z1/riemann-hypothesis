import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0169
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransfer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.killTransfer : KillTransfer := by
  intro I V V' _ _ _ _ _ _ _ ρ ρ' hfin htr x hx
  have h1 : ∀ y : MonoidAlgebra ℂ I,
      LinearMap.trace ℂ V (ρ.asAlgebraHom y) = LinearMap.trace ℂ V' (ρ'.asAlgebraHom y) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g => simpa [Representation.asAlgebraHom_of] using htr g
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  have h2 : ∀ g : I, LinearMap.trace ℂ V (ρ.asAlgebraHom x * ρ g) = 0 := by
    intro g
    have h3 : ρ.asAlgebraHom x * ρ g = ρ.asAlgebraHom (x * MonoidAlgebra.of ℂ I g) := by
      rw [map_mul, Representation.asAlgebraHom_of]
    rw [h3, h1, map_mul, hx, zero_mul, map_zero]
  let b := Module.finBasis ℂ V
  let φ := LinearMap.toMatrixAlgEquiv (R := ℂ) b
  let r : I →* GL (Fin (Module.finrank ℂ V)) ℂ := (φ.toAlgHom.toMonoidHom.comp ρ).toHomUnits
  have hr : ∀ g, ((r g : GL (Fin (Module.finrank ℂ V)) ℂ) : Matrix _ _ ℂ) = φ (ρ g) := by
    intro g
    simp [r, MonoidHom.coe_toHomUnits]
  have hrange : Finite r.range := by
    have hsub : (Set.range r).Finite := by
      refine Set.Finite.of_finite_image (f := fun u : GL (Fin (Module.finrank ℂ V)) ℂ => (u : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ)) ?_
        (fun _ _ _ _ h => Units.ext h)
      refine (hfin.image φ).subset ?_
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨ρ g, ⟨g, rfl⟩, (hr g).symm⟩
    exact hsub.to_subtype
  have hss : IsSSRep r := by
    refine GlobalTheory.ssRep_of_normal_finiteIndex _ _ _ r r.ker inferInstance inferInstance ?_
    intro W _
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    refine ⟨W', ?_, hW'⟩
    intro g v hv
    have hg : r (g : I) = 1 := g.2
    simpa [hg] using hv
  have hspan : ∀ y : MonoidAlgebra ℂ I, φ (ρ.asAlgebraHom y) ∈
      Submodule.span ℂ (Set.range fun g => ((r g : GL (Fin (Module.finrank ℂ V)) ℂ) : Matrix _ _ ℂ)) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      rw [Representation.asAlgebraHom_of, ← hr]
      exact Submodule.subset_span ⟨g, rfl⟩
    | add a c ha hc =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hc
    | smul c a ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha
  have h0 : φ (ρ.asAlgebraHom x) = 0 := by
    refine GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep ℂ I _ r hss _ (hspan x) ?_
    intro g
    rw [hr, ← map_mul, ← h2 g, LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  exact φ.injective (by rw [h0, map_zero])
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.SplitOff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem charpoly_of_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) (hf : ∀ v, f v = c • v) :
    f.charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have e : LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f
      = Matrix.diagonal fun _ => c := by
    ext i j
    simp [LinearMap.toMatrix_apply, hf, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), e, Matrix.charpoly_diagonal]
  simp

theorem UpperTheory.Gal.NearKilling.splitOff :
    SplitOff := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ z c γ q hq hcj h1 h2 h3
  classical
  set f := z.ρ (ineIncl h γ) with hf
  let U : Submodule ℂ V := Module.End.eigenspace f (c γ)
  let R : Submodule ℂ V := LinearMap.range (f - c γ • (1 : Module.End ℂ V))
  let Q : Submodule ℂ V := LinearMap.ker (aeval f q)
  have hUq : ∀ v ∈ U, aeval f q v = q.eval (c γ) • v := fun v hv => by
    by_cases h0 : v = 0
    · simp [h0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hv, h0⟩
  have hUs : ∀ v ∈ U, ∀ s : ↥(Ine (F := E) A), z.ρ (ineIncl h s) v = c s • v := fun v hv s => by
    have k := LinearMap.congr_fun (h1 s) v
    rw [Module.End.mul_apply, hUq v hv, map_smul] at k
    have k2 := (smul_eq_zero.1 k).resolve_left hq
    simpa [sub_eq_zero] using k2
  have hUQ : ∀ v, v ∈ U → v ∈ Q → v = 0 := fun v hv hv' => by
    have k : aeval f q v = 0 := hv'
    rw [hUq v hv] at k
    exact (smul_eq_zero.1 k).resolve_left hq
  have hRQ : R ≤ Q := by
    rintro _ ⟨u, rfl⟩
    exact LinearMap.congr_fun (h2 γ) u
  have hUR : IsCompl U R := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
    · have := LinearMap.finrank_range_add_finrank_ker (f - c γ • (1 : Module.End ℂ V))
      rw [← Module.End.eigenspace_def] at this
      change Module.finrank ℂ R + Module.finrank ℂ U = _ at this
      omega
    · exact Submodule.disjoint_def.2 fun v hv hv' => hUQ v hv (hRQ hv')
  have hQR : Q ≤ R := fun v hv => by
    have : v ∈ U ⊔ R := by rw [hUR.sup_eq_top]; trivial
    obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1 this
    have hu' : u ∈ Q := by
      have := Q.sub_mem hv (hRQ hr)
      simpa using this
    rw [hUQ u hu hu', zero_add]
    exact hr
  have hc : IsCompl Q U := by
    rw [le_antisymm hQR hRQ]
    exact hUR.symm
  have hU : ∀ σ, ∀ v ∈ U, z.ρ σ v ∈ U := fun g v hv => by
    have e : f (z.ρ g v) = z.ρ g (z.ρ (ineIncl h (ineConj g⁻¹ γ)) v) := by
      rw [hf, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ineIncl_ineConj]
      simp [mul_assoc]
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [e, hUs v hv, hcj, map_smul]
  have hQ : ∀ σ, ∀ v ∈ Q, z.ρ σ v ∈ Q := fun g v hv => by
    obtain ⟨u, rfl⟩ := hQR hv
    have e : z.ρ g ((f - c γ • (1 : Module.End ℂ V)) u)
        = (z.ρ (ineIncl h (ineConj g γ)) - c (ineConj g γ) • (1 : Module.End ℂ V)) (z.ρ g u) := by
      have e1 : z.ρ (ineIncl h (ineConj g γ)) (z.ρ g u) = z.ρ g (f u) := by
        rw [hf, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ineIncl_ineConj]
        simp [mul_assoc]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, e1, hcj]
    show aeval f q _ = 0
    rw [e]
    exact LinearMap.congr_fun (h2 (ineConj g γ)) (z.ρ g u)
  let a := z.resZero Q hQ
  let b := z.resZero U hU
  let e := Submodule.prodEquivOfIsCompl Q U hc
  have hb : ∀ (s : ↥(Ine (F := E) A)) (v : U), b.ρ (ineIncl h s) v = c s • v := fun s v =>
    Subtype.ext (hUs v v.2 s)
  have ha : ∀ v, a.ρ (ineIncl h γ) v = c γ • v → v = 0 := fun v hv => by
    have k : z.ρ (ineIncl h γ) (v : V) = c γ • (v : V) := congrArg Subtype.val hv
    exact Subtype.ext (hUQ v (Module.End.mem_eigenspace_iff.2 k) v.2)
  have hg : ∀ σ v, e.symm (z.ρ σ v) = (a.sum b).ρ σ (e.symm v) := fun σ v => by
    obtain ⟨p, rfl⟩ := e.surjective v
    rw [e.symm_apply_apply, LinearEquiv.symm_apply_eq]
    simp [e, a, b, Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]
  have h0 : ∀ v, z.N (e.symm.symm (0, v)) = 0 := fun v => by
    have k : e.symm.symm (0, v) = (v : V) := by simp [e, Submodule.coe_prodEquivOfIsCompl']
    rw [k]
    exact h3 v (hUs v v.2)
  obtain ⟨a', ea⟩ := UpperTheory.GalN.exists_sum z a b e.symm hg rfl (ineIncl h γ) (deg_ineIncl _) (c γ) (hb γ) ha h0
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ Module.finrank ℂ U :=
    fun s => charpoly_of_scalar _ _ (hb s)
  have hm : f.charpoly.rootMultiplicity (c γ) = Module.finrank ℂ U := by
    have k := z.charpoly_eq_mul_of_isCompl Q U hQ hU hc (ineIncl h γ)
    have hne := (LinearMap.charpoly_monic (a.ρ (ineIncl h γ))).ne_zero
    have hroot : ¬ (a.ρ (ineIncl h γ)).charpoly.IsRoot (c γ) := fun hr => by
      have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hr
      obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
      exact hv0 (ha v (Module.End.mem_eigenspace_iff.1 hv))
    rw [hf, k]
    show ((a.ρ (ineIncl h γ)).charpoly * (b.ρ (ineIncl h γ)).charpoly).rootMultiplicity (c γ) = _
    rw [hbc γ, rootMultiplicity_mul (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero),
      rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hroot, zero_add]
  rw [hm]
  refine ⟨WD.mk a', WD.mk b, by rw [WD.lpSum_mk]; exact ea, WD.lpDim_mk b, (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 rfl, fun σ hσ => ?_⟩
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk]
  exact hbc ⟨σ, hσ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.TypeNear
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori

namespace UpperTheory.Gal.NearKilling

def TypeNear (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      NearTr r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun i s => ι.symm (η (blockOf d hd i) (art (ineIncl h s)))) ∧
      ∀ b₀, NearKills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun s => ι.symm (η b₀ (art (ineIncl h s))))
        fun b s => ι.symm (η (b₀.succAbove b) (art (ineIncl h s)))

def IAType (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ∀ hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal,
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      InePol (wdOf h hl ι r) (fun i s => η (blockOf d hd i) (art (ineIncl h s))) ∧
      ∀ b₀, (∀ b, b ≠ b₀ → θ b ≠ θ b₀) → EigZero (wdOf h hl ι r) fun s => η b₀ (art (ineIncl h s))

def IA : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → UpperTheory.GalS.TmW (rc (algNorm σ)) →
      IneRel (wdOf h hl ι r) (rc (algNorm σ))

end UpperTheory.Gal.NearKilling
end
end

