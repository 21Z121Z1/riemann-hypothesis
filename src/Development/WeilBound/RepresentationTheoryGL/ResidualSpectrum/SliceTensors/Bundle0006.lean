import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0005
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.FrobRecipHolds
section
noncomputable section

open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs

namespace SliceFrobeniusReciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {n : Fin c → ℕ} {h : ∑ i, n i = N} {σ' : SmIrr (GL (Fin N) k)} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W} {ℓ : σ'.V →ₗ[ℂ] W}

def frobFun (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) :
    IndSp (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹) :=
  ⟨⟨fun g => ℓ (σ'.ρ g v), fun p g => by
      show ℓ (σ'.ρ ((p : GL (Fin N) k) * g) v) = _
      rw [map_mul, Module.End.mul_apply, hℓ p]
      simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, smul_smul, ← Units.val_mul,
        MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((σ'.smooth v).mem_nhds (by simp)) fun g hg => by
      have hg' : σ'.ρ g v = v := hg
      show _ = _
      apply Subtype.ext
      funext x
      show ℓ (σ'.ρ (x * g) v) = ℓ (σ'.ρ x v)
      rw [map_mul, Module.End.mul_apply, hg'])⟩

theorem frobFun_apply (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) (g : GL (Fin N) k) :
    (frobFun hℓ v).1.1 g = ℓ (σ'.ρ g v) := rfl

def frobMap (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) :
    σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)) where
  toLinearMap :=
    { toFun := frobFun hℓ
      map_add' := fun v v' => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (v + v')) = ℓ (σ'.ρ g v) + ℓ (σ'.ρ g v')
        simp))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (a • v)) = a • ℓ (σ'.ρ g v)
        simp)) }
  isIntertwining' g := by
    ext v x
    show ℓ (σ'.ρ x (σ'.ρ g v)) = ℓ (σ'.ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

end SliceFrobeniusReciprocity

open SliceFrobeniusReciprocity in
theorem frobRecip_holds : PositivityTheory.RSHS.LS.FrobRecip := by
  intro k _ _ _ _ N c n h σ' W _ _ ρ ℓ hℓ0 hℓ
  refine ⟨frobMap hℓ, fun h0 => hℓ0 (LinearMap.ext fun v => ?_)⟩
  have h1 := congrArg (fun f : _ →ₗ[ℂ] _ => (f v).1.1 1) h0
  simpa [frobMap, frobFun_apply] using h1

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LocSubOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.LsTop

open PositivityTheory.RSHS.LS

theorem comp_ne {G U V W : Type} [Monoid G] [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {a : Representation ℂ G U} {b : Representation ℂ G V} {c : Representation ℂ G W}
    (g : a.IntertwiningMap b) (hg : g.toLinearMap ≠ 0) (Φ : b.Equiv c) : ∃ f : a.IntertwiningMap c, f ≠ 0 := by
  refine ⟨Φ.toIntertwiningMap.comp g, fun h0 => hg ?_⟩
  refine LinearMap.ext fun v => Φ.toLinearEquiv.injective ?_
  have h1 := congrArg (fun q : a.IntertwiningMap c => q v) h0
  simpa using h1

theorem step1 (hR : RestrictAtPoint) (hP : ExistsProj) (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (N c : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E))
    (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))) (hτ : ∀ i, (π i).IsLocComp w (τ i))
    (V : Submodule ℂ (Sm E N)) (hE : Emb V (· ∈ indForms h π)) (σ' : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (hσ' : IsLocCompGL V w σ') :
    ∃ ℓ : σ'.V →ₗ[ℂ] PiTensorProduct ℂ fun i => (τ i).V, ℓ ≠ 0 ∧
      ∀ (p : parab (w.adicCompletion E) (stdBlocks n h)) (v : σ'.V),
        ℓ (σ'.ρ p v) = piTensor (fun i => (τ i).ρ) (leviProj (w.adicCompletion E) (stdBlocks n h) p) (ℓ v) := by
  obtain ⟨e, he1, he2, he3⟩ := hE
  obtain ⟨f, hf0, hfV, hfeq⟩ := hσ'
  let F : PositivityTheory.RSHS.LeviInductionForms.LocMaps (indForms h π) w σ'.ρ :=
    ⟨e ∘ₗ f, fun v => he1 _ (hfV v), fun g v => by
      simp only [LinearMap.comp_apply]
      rw [hfeq g v]
      exact he3 (.fin _) _ (hfV v)⟩
  have hF0 : F.1 ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    exact he2 _ (hfV v) (LinearMap.congr_fun h0 v)
  obtain ⟨L, hLT, hL0, hLeq⟩ := hR E N c n h π w σ'.V σ'.ρ F hF0
  obtain ⟨v0, hv0⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    exact hL0 (LinearMap.ext fun v => not_not.1 fun hv => hc ⟨v, hv⟩)
  obtain ⟨p, hp0, hpeq⟩ := hP E c n π w τ hτ (L v0) (hLT v0) hv0
  refine ⟨p ∘ₗ L, fun h0 => hp0 (LinearMap.congr_fun h0 v0), fun q v => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hLeq q v]
  exact hpeq _ _ (hLT v)

theorem hst_rev (a d : ℕ) (i : Fin d) :
    ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) =
      ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 + (((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ)) := by
  rw [PositivityTheory.RSHS.LocalComponentTwist.modExp_const, Fin.val_rev]
  have hi := i.2
  have hc : ((d - ((i : ℕ) + 1) : ℕ) : ℂ) = (d : ℂ) - ((i : ℕ) : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc]
  unfold spehExp
  push_cast
  ring

theorem gen (hF : FrobRecip) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N a d : ℕ) (h : ∑ _ : Fin d, a = N) (σ : SmIrr (GL (Fin a) k)) (σ' : SmIrr (GL (Fin N) k))
    (ψ : Fin d → GL (Fin a) k →* ℂˣ)
    (hψ : ∀ i, ψ i = detChar (Fin a) (absPow k ((-spehExp d i + a * spehExp d i : ℝ) : ℂ)))
    (ℓ : σ'.V →ₗ[ℂ] PiTensorProduct ℂ fun _ : Fin d => σ.V) (h0 : ℓ ≠ 0)
    (hℓ : ∀ (p : parab k (stdBlocks (fun _ : Fin d => a) h)) (v : σ'.V), ℓ (σ'.ρ p v) =
      piTensor (fun i => GlobalTheory.SmGL.twist σ.ρ (ψ i)) (leviProj k (stdBlocks (fun _ : Fin d => a) h) p) (ℓ v)) :
    ∃ hd : ∑ i : Fin d, (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (prodIrr (fun i : Fin d => spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd),
        f ≠ 0 := by
  have hx := hF k N d (fun _ => a) h σ' (PiTensorProduct ℂ fun _ : Fin d => σ.V)
    (piTensor (Γ := fun _ : Fin d => GL (Fin a) k) (X := fun _ : Fin d => σ.V) fun i => GlobalTheory.SmGL.twist σ.ρ (ψ i)) ℓ h0 hℓ
  have hy := PositivityTheory.RSHS.LocalComponentTwist.levi_equiv σ.ρ (fun i : Fin d => ((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ))
    (fun i => ((-spehExp d i + a * spehExp d i : ℝ) : ℂ)) (hst_rev a d) ψ hψ
  refine hx.elim fun g hg => hy.elim fun φ => ?_
  let T : ∀ i : Fin d, (GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - ((i.rev : ℕ) : ℂ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨h, comp_ne g hg ((GlobalTheory.LocGL.parIndEquiv (stdBlocks (fun _ : Fin d => a) h) φ).symm.trans M)⟩

theorem locSub_of (hR : RestrictAtPoint) (hP : ExistsProj) (hF : FrobRecip) : LocSub :=
  fun E _ _ _ N a d V π _ _ hA w σ σ' hσ hσ' =>
    hA.elim fun h hA => hA.elim fun ν hA =>
      (step1 hR hP E N d (fun _ => a) h (fun i => π.twist (ν i)) w
        (fun i => σ.twist (CuspSub.locDet a (ν i) w) (CuspSub.isOpen_ker_locDet (ν i) w))
        (fun i => PositivityTheory.RSHS.LocalComponentTwist.isLocComp_twist π (ν i) hσ) V hA.2 σ' hσ').elim fun ℓ hℓ =>
      gen hF (w.adicCompletion E) N a d h σ σ' (fun i => CuspSub.locDet a (ν i) w)
        (fun i => congrArg (fun χ : (w.adicCompletion E)ˣ →* ℂˣ => χ.comp Matrix.GeneralLinearGroup.det)
          (PositivityTheory.RSHS.LocalComponentTwist.loc_eq_absPow (hA.1 i) w)) ℓ hℓ.1 hℓ.2

end PositivityTheory.Rg.Rs.LsTop

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreD
section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem heckeVec_apply {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {F : Sm E N}
    {f : GL (Fin N) (w.adicCompletion E) → ℂ} (hf : f ∈ Hecke ℂ (KGL w N)) (y : GA E N) :
    (heckeVec ((finRep E N).comp (locGL E N w)) (KGL w N) f F).1 y =
      heckeVec (rightReg ℂ _ ℂ) (KGL w N) f (fun g => F.1 (y * finGL E N (locGL E N w g))) 1 := by
  have hK := Final.GLintComm E w N
  rw [heckeVec, heckeVec]
  have e1 := ((LinearMap.proj (R := ℂ) (φ := fun _ : GA E N => ℂ) y).comp (Sm E N).subtype).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf ((finRep E N).comp (locGL E N w)) F)
  have e2 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin N) (w.adicCompletion E) => ℂ)
    (1 : GL (Fin N) (w.adicCompletion E))).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf (rightReg ℂ _ ℂ) (fun g => F.1 (y * finGL E N (locGL E N w g))))
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  show f c.out • F.1 (y * finGL E N (locGL E N w c.out)) = f c.out • F.1 (y * finGL E N (locGL E N w (1 * c.out)))
  rw [one_mul]

def evAt {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) : U →ₗ[ℂ] ℂ :=
  LinearMap.proj x ∘ₗ (Sm E m).subtype ∘ₗ U.subtype

@[simp] theorem evAt_apply {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) (ψ : U) : evAt U x ψ = ψ.1.1 x := rfl

theorem exists_tensor {c : ℕ} {n : Fin c → ℕ} (U : ∀ i, Submodule ℂ (Sm E (n i)))
    {Φ : (∀ i, GA E (n i)) → ℂ} (hΦ : Φ ∈ GlobalTheory.BCWords.tensorSp U) :
    ∃ v : ⨂[ℂ] i, U i, ∀ m, Φ m = evT (fun i => evAt (U i) (m i)) v := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨PiTensorProduct.tprod ℂ φ, fun m => by rw [evT_tprod]; rfl⟩
  | zero => exact ⟨0, fun m => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hy
    exact ⟨v + v', fun m => by rw [Pi.add_apply, hv, hv', map_add]⟩
  | smul a x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨a • v, fun m => by rw [Pi.smul_apply, hv, map_smul, smul_eq_mul]⟩

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

