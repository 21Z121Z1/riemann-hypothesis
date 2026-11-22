import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLat
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSerA
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutProdA
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem cut_char (hB : B.IsGood σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (hres : ResEtaF χ m) (hε : IsHalfF σ ε) {e : AEF F E} (he : IsSplitIdemF σ e)
    {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g) (hx : IsDetAtF σ e J g x) :
    χ (GlobalTheory.SplitDetCharF.cutDet σ J ε hε.idem g) = χ x := by
  rcases hε.split e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [GlobalTheory.SplitDetCharF.cutDet_same ε hε.idem a1 a2 hg hx]
  · exact GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hB.cm hres _ x
      (GlobalTheory.SplitDetCharF.cutDet_conj hJ ε hε.idem he.1 a1 a2 hg hx)

theorem exists_fin_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (h1 : IsHeckeCharF η)
    (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) : ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) := by
  have hB := C.good
  have hreal := GlobalTheory.T.latticeIntertwinerRep_trivial_realPoints F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hheis := GlobalTheory.T.latticeIntertwinerRep_normalizes_heisenberg_finite F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hcont := GlobalTheory.T.latticeIntertwinerRep_continuous_group F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hunit := GlobalTheory.T.lintegral_sq_latticeModelRep_fundamentalDomain F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hsplit := GlobalTheory.T.latticeIntertwinerRep_splitPlace_positive_scalar F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  let z : GAF σ JS × GAF σ JT → Circle := zF σ JS JT η ε hε.idem
  have z1 : z 1 = 1 := by simp [z, zF]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, zF, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := by
    show Continuous fun p : GAF σ JS × GAF σ JT =>
      ((η ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε hε.idem p.1))⁻¹ * (η ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε hε.idem p.2)
    exact ((isHeckeCharF_pow h1 nT).1.comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_fst)).inv.mul
      ((isHeckeCharF_pow h1 nS).1.comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_snd))
  obtain ⟨om, hom⟩ := exists_extend (thetaSubF σ JS JT ξ₀ B.ψ)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ))
  have ho : ∀ p f (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f),
      om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WOF F E nS nT → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩, fun p f => hom p f⟩
  · rw [ho p f hf]
    exact (thetaSubF σ JS JT ξ₀ B.ψ).smul_mem _ (Om p ⟨f, hf⟩).2
  · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
    exact (continuous_subtype_val.comp z3).mul (hcont ⟨f, hf⟩ u)
  · rw [← hunit μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
    refine lintegral_congr fun u => ?_
    rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · rw [ho _ f hf, hreal g hg k hk, show z (g, k) = 1 by
      simp [z, zF, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin g hg, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin k hk],
      Circle.coe_one, one_smul]
  · have hf' := GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 u f hf
    rw [ho _ f hf, ho _ _ hf', heisOF_smul, hheis g hg k hk u ⟨f, hf⟩ ⟨_, hf'⟩ rfl]
  · obtain ⟨r, hr, h1⟩ := hsplit e he g k hg hk
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacOF (η ^ nS) (η ^ nT) x y by
        simp only [z, zF, splitFacOF, cut_char hB C.hS (resEtaF_pow h2 nT) hε he hg hx,
          cut_char hB C.hT (resEtaF_pow h2 nS) hε he hk hy]]
    ring

theorem fin_inf_comm_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  have hσ : ∀ x, σ (σ x) = x := LatA.sig_sig C.good
  obtain ⟨a, ha, k, hk, e1, -⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS q.1
  obtain ⟨b, hb, l, hl, e2, -⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT q.2
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi q f = oi (a, b) f := fun f h => by
    rw [show q = (a, b) * (k, l) from Prod.ext e1 e2, map_mul, Module.End.mul_apply, hi.triv k hk l hl f h]
  let L : thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] thetaSubF σ JS JT ξ₀ B.ψ := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val ((LatA.rep hO).comm (LatA.sys hσ C.hS C.hT C.hξ hO) L (fun x v => Subtype.ext (by
    have e3 : actOF σ JS JT a b x = x := by
      have := congrArg (fun y : XFF F E nS nT => (y : WOF F E nS nT)) (LatA.rhoFF_real ha hb x)
      rwa [coe_rhoFF] at this
    rw [hL, coe_opFF, coe_opFF, hL, map_smul, hoi _ (hc _ _ v.2), hi.Heisenberg₂ a ha b hb _ _ v.2, e3, ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)

theorem eventually_smul_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∃ c : ℂ, of p f = c • f := by
  filter_upwards [LatA.eventually_fix (LatA.sig_sig C.good) C.hS C.hT C.hξ hO ⟨f, h1⟩] with p hp
  obtain ⟨c, hc'⟩ := hof p
  exact ⟨c, by rw [hc' ⟨f, h1⟩, hp]⟩

theorem continuous_product_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f)
    (u : WOF F E nS nT) : Continuous fun p : GAF σ JS × GAF σ JT => of p (oi p f) u := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))
  haveI : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul_A C hO hof h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    rw [fin_inf_comm_A C hO hof hi p p f h1, hc', h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm_A C hO hof hi p p f h1, hc', map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

theorem datum_of_aut_A (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hη : IsHeckeCharF η) (hres : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  have hB := C.good
  have hψ := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  have hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f) :=
    fun p q f h => fin_inf_comm_A C hO hof hi p q f h
  have hth : ∀ (w₀ : WOF F E nS nT) f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
      IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) :=
    fun w₀ f h => GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 w₀ f h
  let Th := thetaSubF σ JS JT ξ₀ B.ψ
  let Om2 : GAF σ JS × GAF σ JT →* Module.End ℂ Th :=
    { toFun := fun p => (of p * oi p).restrict (p := Th) (q := Th) fun f h1 => hf.pres p _ (hi.pres p f h1)
      map_one' := LinearMap.ext fun f => Subtype.ext (by
        show of 1 (oi 1 f) = f
        simp only [map_one, Module.End.one_apply])
      map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
        show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q (f : WOF F E nS nT → ℂ))))
        simp only [map_mul, Module.End.mul_apply]
        rw [hcomm q p _ (hi.pres q _ f.2)]) }
  obtain ⟨om, hom⟩ := exists_extend Th Om2
  have ho : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  refine ⟨om, hψ, isHeckeCharF_pow hη _, isHeckeCharF_pow hη _, resEtaF_pow hres _, resEtaF_pow hres _, hp,
    fun g h w₀ f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 w => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨a, ha, k, hk, e1, e1'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS g
    obtain ⟨b, hb, l, hl, e2, e2'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT h
    have key : ∀ x, IsThetaFunOF σ JS JT ξ₀ B.ψ x → om (g, h) x = of (k, l) (oi (a, b) x) := fun x hx => by
      rw [ho _ x hx]
      have E1 : ((g, h) : GAF σ JS × GAF σ JT) = (a, b) * (k, l) := Prod.ext e1 e2
      have E2 : ((g, h) : GAF σ JS × GAF σ JT) = (k, l) * (a, b) := Prod.ext e1' e2'
      have E3 : oi (g, h) x = oi (a, b) x := by rw [E1, map_mul, Module.End.mul_apply, hi.triv k hk l hl x hx]
      rw [E3, E2, map_mul, Module.End.mul_apply, hf.triv a ha b hb _ (hi.pres _ x hx)]
    rw [key _ (hth w₀ f h1), key f h1, hi.Heisenberg₂ a ha b hb w₀ f h1, hf.Heisenberg₂ k hk l hl _ _ (hi.pres _ f h1),
      ← actOF_mul, ← e1', ← e2']
  · rw [ho _ f h1]
    exact haut γ hγ γ' hγ' f h1
  · have e : (fun p => om p f w) = fun p => of p (oi p f) w := funext fun p => by rw [ho p f h1]
    rw [e]
    exact continuous_product_A C hO hf hof hi h1 w
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [ho _ f h1, hi.triv g (mem_GfCF_of_suppAt he hg) h (mem_GfCF_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealA
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF GlobalTheory.RealWeil

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem ev_fderivF (hc : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (G : BBF σ JS JT ξ₀ ψ)
    (hG : Sm (rhoVF σ JS JT ξ₀ ψ hc ι) G) (z : IxF F nS nT → ℂ) (w : WOF F E nS nT) :
    (fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z).1 w =
      deriv (fun t : ℝ => heisOF σ JS JT ξ₀ ψ (iotaVF ι (t • z)) G.1 w) 0 := by
  have hd : DifferentiableAt ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 :=
    (hG.differentiable (by simp)).differentiableAt
  let L : ↥(BBF σ JS JT ξ₀ ψ) →L[ℝ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ w).comp (BBF σ JS JT ξ₀ ψ).subtypeL).restrictScalars ℝ
  have hline : HasDerivAt (fun t : ℝ => t • z) z 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
  have h2 : HasDerivAt (fun t : ℝ => rhoVF σ JS JT ξ₀ ψ hc ι (t • z) G)
      (fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z) 0 := by
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact h
  have h3 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  exact h3.deriv.symm

theorem fderiv_vacF (hc : IsCharAF F ψ) (ι : (InfinitePlace F → ℂ) →+ AEF F E) (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (G : BBF σ JS JT ξ₀ ψ) (hG : Sm (rhoVF σ JS JT ξ₀ ψ hc ι) G) (hv : IsVacF σ JS JT ξ₀ ψ ι s G.1)
    (z : IxF F nS nT → ℂ) :
    fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 z +
      Complex.I • fderiv ℝ (fun v => rhoVF σ JS JT ξ₀ ψ hc ι v G) 0 (Complex.I • s *ᵥ z) = 0 := by
  apply Subtype.ext
  ext w
  have h1 := ev_fderivF hc ι G hG z w
  have h2 := ev_fderivF hc ι G hG (Complex.I • s *ᵥ z) w
  have h3 := hv w z
  rw [PositivityTheory.ThKW.jV_apply] at h3
  simp only [Submodule.coe_add, Submodule.coe_smul, BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul, Pi.add_apply, smul_eq_mul, Submodule.coe_zero,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  rw [h1, h2]
  exact h3

variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem exists_inf_A (C : Ctx σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  obtain ⟨good, hS, hT, h0, hξ, hinf, hchart⟩ := C
  obtain ⟨hc, -⟩ := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B good
  obtain ⟨hHh, hHd⟩ := GlobalTheory.T.hermitianFormRealCoordinateMatrix_hermitian_det_ne_zero F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ
  have hheis : GlobalTheory.RealWeil.IsHeis
      (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ (HMF JS JT ξ₀ (tauB B)).mulVec x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    unfold GlobalTheory.RealWeil.IsHeis
    simp only [GlobalTheory.RealWeilF.rhoVF]
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => ?_, fun f => ?_⟩
    · rw [iotaVF_zero, rhoBF_zero]
    · rw [rhoBF_rhoBF, iotaVF_add,
        GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart u v]
    · exact norm_rhoBF hc _ f
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hc f).comp (continuous_iotaVF hchart)
  obtain ⟨Ω, hosc, hone1, hcont, hvac⟩ := GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (IxF F nS nT) (HMF JS JT ξ₀ (tauB B)) hHh hHd
    (↥(BBF σ JS JT ξ₀ B.ψ)) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hheis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
    (GlobalTheory.T.realCoordinateAction_unitary_preserves_hermitianForm F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart)
  obtain ⟨hadd, hsmul, hsmp, hone, hmul, hequiv, hcomm7, hnorm⟩ := hosc
  have hSmθ : ∀ x : ↥(BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) →
      GlobalTheory.RealWeil.Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) x := fun x hx =>
    GlobalTheory.T.thetaFunction_smoothVector_realHeisenberg F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart hc x hx
  have hcommA : ∀ u : WOF F E nS nT, Matrix.map u ⇑(infPartF F E) = 0 →
      ∀ (v : IxF F nS nT → ℂ) (z : ↥(BBF σ JS JT ξ₀ B.ψ)),
        rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v z) =
          rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u z) := by
    intro u hu v z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ u (iotaVF ι v) hu (real_iotaVF hchart v)
    simp only [GlobalTheory.RealWeilF.rhoVF]
    rw [rhoBF_rhoBF, rhoBF_rhoBF, h1, h2, add_comm u (iotaVF ι v)]
  have hfix : ∀ (u : WOF F E nS nT) (z : ↥(BBF σ JS JT ξ₀ B.ψ)),
      heisOF σ JS JT ξ₀ B.ψ u ⇑(z : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑(z : BoundedContinuousFunction (WOF F E nS nT) ℂ) → rhoBF σ JS JT ξ₀ B.ψ hc u z = z := by
    intro u z hz
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [coe_rhoBF, hz]
  have hth : ∀ p (x : ↥(BBF σ JS JT ξ₀ B.ψ)), IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) →
      IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑((Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) := by
    intro p x hx
    have hsm := hSmθ x hx
    obtain ⟨-, ⟨U, hU, hUx⟩, -, -⟩ := hx
    refine GlobalTheory.T.isThetaFun_of_smooth_real_heisenberg_level F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart hc (Ω p x) (hsmp p x hsm)
      ⟨U, hU, fun u hu hu0 => ?_⟩
    have hA : rhoBF σ JS JT ξ₀ B.ψ hc u x = x := hfix u x (hUx u hu hu0)
    have h7 := hcomm7 p (rhoBF σ JS JT ξ₀ B.ψ hc u) (fun v f => hcommA u hu0 v f) x hsm
    rw [hA] at h7
    rw [← coe_rhoBF hc u (Ω p x), ← h7]
  obtain ⟨om, hom⟩ := GlobalTheory.RealWeilF.exists_homF (GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc) Ω hth
    (fun p x x' hx hx' => hadd p x x' (hSmθ x hx) (hSmθ x' hx'))
    (fun p a x hx => hsmul p a x (hSmθ x hx))
    (fun x hx => hone x (hSmθ x hx))
    (fun p p' x hx => hmul p p' x (hSmθ x hx))
  have hx : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ x : ↥(BBF σ JS JT ξ₀ B.ψ), ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) = f := by
    intro f hf
    have hb := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hc f hf
    obtain ⟨hq, -, hcf, -⟩ := hf
    exact ⟨GlobalTheory.RealWeilF.toBF f hcf hb hq, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩,
    fun g hg h hh f hf => ?_, fun g hg h hh w₀ f hf => ?_⟩, fun s hss hpos p hsp f hf hv => ?_⟩
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom p x hf]
    exact hth p x hf
  · obtain ⟨x, rfl⟩ := hx f hf
    have e : (fun p => om p ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) w) = fun p => (↑(Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) w :=
      funext fun p => by rw [hom p x hf]
    rw [e]
    exact (BoundedContinuousFunction.evalCLM ℂ w).continuous.comp
      (continuous_subtype_val.comp (hcont (GlobalTheory.T.continuous_adelicAction_realCoordinates F E σ B good nS nT JS JT θ hinf) x (hSmθ x hf)))
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [show om p ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑((Ω p x) : BoundedContinuousFunction (WOF F E nS nT) ℂ) from hom p x hf]
    exact GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 x (Ω p x)
      (fun Hs _ _ _ Φ hΦ => hnorm Hs Φ (fun v g => hΦ (iotaVF ι v) g) p x (hSmθ x hf))
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom (g, h) x hf, hone1 (g, h) (mMF_fin θ hg hh) x (hSmθ x hf)]
  · obtain ⟨x, rfl⟩ := hx f hf
    obtain ⟨u, v, hu, rfl⟩ := GlobalTheory.T.exists_finiteAdelic_add_realChartPoint F E nS nT θ ι hchart w₀
    have hθ0 := GlobalTheory.T.theta_function_heisenberg_invariant F E σ B good nS nT JS JT ξ₀ (u + iotaVF ι v) ⇑(x : BoundedContinuousFunction (WOF F E nS nT) ℂ) hf
    obtain ⟨y, hy⟩ := hx _ hθ0
    have hyθ : IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑(y : BoundedContinuousFunction (WOF F E nS nT) ℂ) := by rw [hy]; exact hθ0
    have hsym := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ u (iotaVF ι v) hu (real_iotaVF hchart v)
    have hyx : y = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v x) := by
      apply Subtype.ext
      apply DFunLike.coe_injective
      show ⇑(y : BoundedContinuousFunction (WOF F E nS nT) ℂ) = ⇑((rhoBF σ JS JT ξ₀ B.ψ hc u (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) x)) : BoundedContinuousFunction (WOF F E nS nT) ℂ)
      rw [hy, coe_rhoBF, coe_rhoBF, heisOF_heisOF, hsym.1, AddChar.map_zero_eq_one, one_smul]
    have hsmv : GlobalTheory.RealWeil.Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) (rhoVF σ JS JT ξ₀ B.ψ hc ι v x) := by
      apply hSmθ
      show IsThetaFunOF σ JS JT ξ₀ B.ψ ⇑((rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) x) : BoundedContinuousFunction (WOF F E nS nT) ℂ)
      rw [coe_rhoBF]
      exact GlobalTheory.T.theta_function_heisenberg_invariant F E σ B good nS nT JS JT ξ₀ (iotaVF ι v) _ hf
    rw [← hy, hom (g, h) y hyθ, hyx, hcomm7 (g, h) _ (hcommA u hu) _ hsmv, hequiv (g, h) v x (hSmθ x hf),
      GlobalTheory.RealWeilF.actOF_add, GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms F E σ nS nT JS JT g h hg hh u hu,
      GlobalTheory.T.adelicHomAction_realCoordinates_eq F E σ B good nS nT JS JT hS hT ξ₀ h0 hξ θ hinf ι hchart g h v, hom (g, h) x hf]
    have hsym2 := GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal F E σ nS nT JS JT ξ₀ u
      (iotaVF ι ((mMF σ JS JT θ (g, h)).mulVec v)) hu (real_iotaVF hchart _)
    show ⇑((rhoBF σ JS JT ξ₀ B.ψ hc u (rhoBF σ JS JT ξ₀ B.ψ hc
      (iotaVF ι ((mMF σ JS JT θ (g, h)).mulVec v)) (Ω (g, h) x))) : BoundedContinuousFunction (WOF F E nS nT) ℂ) = _
    rw [coe_rhoBF, coe_rhoBF, heisOF_heisOF, hsym2.1, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨x, rfl⟩ := hx f hf
    rw [hom p x hf, hvac s p hss hpos hsp x (hSmθ x hf) (fun z => fderiv_vacF hc ι s x (hSmθ x hf) hv z)]
    rfl

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSer
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem ser_vacuum (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) :=
  SerA.main C hG hR hO hs a

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitCoef
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

theorem unit_coef : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (w₀ : WOF F E nS (nT + nT)) (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

