import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrOff

theorem idem_apply_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (a : FiniteAdeleRing (𝓞 E) E) (ha : a * a = a)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 →
      ¬ ∀ Q, Valued.v ((a * algebraMap E (FiniteAdeleRing (𝓞 E) E) ((x : E)⁻¹)) Q) ≤ 1) : a P = 1 := by
  have h01 : ∀ Q, a Q ≠ 0 → a Q = 1 := fun Q hQ =>
    mul_left_cancel₀ hQ (by rw [← GlobalTheory.PlaceIdem.mul_ap, ha, mul_one])
  refine h01 P fun h0 => ?_
  obtain ⟨n, hn, x, hx⟩ := GlobalTheory.IdemRes.exists_pow_eq_span P.asIdeal P.ne_bot
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
    exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)
  refine h x (Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x)) hx0 fun Q => ?_
  rw [GlobalTheory.PlaceIdem.mul_ap]
  by_cases hQ : a Q = 0
  · rw [hQ, zero_mul, map_zero]; exact zero_le
  · rw [h01 Q hQ, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one Q hx0]
    intro hxQ
    have := Q.isPrime
    have h1 : P.asIdeal ^ n ≤ Q.asIdeal := by rw [hx]; exact (Ideal.span_singleton_le_iff_mem _).2 hxQ
    have h2 : P.asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le h1
    have h3 : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h2)
    exact hQ (h3 ▸ h0)

variable {D : D7}

theorem exists_conj_mem {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {x : 𝓞 D.host.E}
    (hx : x ∈ P'.asIdeal) : ∃ y ∈ P.asIdeal, D.sp.cm.sig (y : D.host.E) = (x : D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hs : ∀ y, (s y : D.host.E) = star (y : D.host.E) := fun _ => rfl
  have hle : P.asIdeal ≤ P'.asIdeal.comap s := fun c hc => by
    obtain ⟨c', hc', e⟩ := h c hc
    have : s c = c' := RingOfIntegers.ext (by rw [hs, e])
    rw [Ideal.mem_comap, this]; exact hc'
  have he := P.isMaximal.eq_of_le (Ideal.comap_ne_top s P'.isPrime.ne_top) hle
  have hss : s (s x) = x := RingOfIntegers.ext (by rw [hs, hs, star_star])
  refine ⟨s x, ?_, congrArg Subtype.val hss⟩
  rw [he, Ideal.mem_comap, hss]; exact hx

section
variable (ι : (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  (h1 : ∀ x : D.host.E, ι ((1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
  (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
include h1 h2

theorem comp_eq_one {f : AE D} (hf : f * f = f) (P : Pl D.host.E)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 → finPart D (f * incA D ((x : D.host.E)⁻¹)) ∉ intAE D) :
    ι (finPart D f) P = 1 := by
  refine idem_apply_eq_one P _ (by rw [← map_mul, ← RingHom.map_mul, hf]) fun x hx hx0 hc => h x hx hx0 ?_
  have e : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
  rw [h2, RingHom.map_mul, map_mul, e, h1]
  exact hc

theorem comp_idem {f : AE D} {P : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P) : ι (finPart D f) P = 1 :=
  comp_eq_one ι h1 h2 hf.1.1 P fun x hx hx0 => (hf.2 x hx0).1 hx

theorem comp_conj_idem {f : AE D} {P P' : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P)
    (hc : Formalism.IndefR.Lev.IsConjPl P P') : ι (finPart D (cA D f)) P' = 1 := by
  refine comp_eq_one ι h1 h2 (by rw [← RingHom.map_mul, hf.1.1]) P' fun x hx hx0 hi => ?_
  obtain ⟨y, hy, hyx⟩ := exists_conj_mem hc hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (RingOfIntegers.ext (hyx.symm.trans (map_zero _)))
  refine (hf.2 y hy0).1 hy ?_
  have e : cA D (incA D ((y : D.host.E)⁻¹)) = incA D ((x : D.host.E)⁻¹) := by
    rw [← hyx, ← map_inv₀ D.sp.cm.sig]; rfl
  rw [← e, ← RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA] at hi
  have := GlobalTheory.PlaceIdem.sig_mem D hi
  rwa [GlobalTheory.PlaceIdem.sig_sig] at this

end

theorem exists_idem_mul {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f PP ∧ f * (e + cA D e) = f ∧ cA D f * (e + cA D e) = cA D f := by
  obtain ⟨⟨es, h1, h2⟩, h3⟩ := he
  have h4 : es PP * e = es PP := by
    rw [h2]
    refine GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij => ?_) hPP
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]
  have h5 : es PP * (e + cA D e) = es PP := by
    rw [mul_add, h4, ← h4, mul_assoc, h3, mul_zero, add_zero]
  refine ⟨es PP, h1 PP hPP, h5, ?_⟩
  have h6 := congrArg (cA D) h5
  rwa [RingHom.map_mul, RingHom.map_add, cA_cA, add_comm] at h6

theorem unrOff_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  intro D c χ P₀ e hc he hu x hx1 hx2 hx3 hb
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have hone : ∀ (f : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), f * (e + cA D e) = f → ι (finPart D f) P = 1 →
      ι (finPart D (x : AE D)) P = 1 := by
    intro f P hf hP
    have e1 : f * (x : AE D) = f := by rw [← hf, mul_assoc, hb]
    have e2 : ι (finPart D f) * ι (finPart D (x : AE D)) = ι (finPart D f) := by
      rw [← map_mul, ← RingHom.map_mul, e1]
    have e3 : ι (finPart D f) P * ι (finPart D (x : AE D)) P = ι (finPart D f) P :=
      congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e2
    rwa [hP, one_mul] at e3
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 1 → χ.UnrAt P := by
    intro P hP
    refine hu P (fun hm => hP ?_) fun PP hm hcj => hP ?_
    · obtain ⟨f, f1, f2, -⟩ := exists_idem_mul he hm
      exact hone f P f2 (comp_idem ι h1 h2 f1)
    · obtain ⟨f, f1, -, f3⟩ := exists_idem_mul he hm
      exact hone _ P f3 (comp_conj_idem ι h1 h2 f1 hcj)
  have key := hprod x hx1 S (fun P => if ι (finPart D (x : AE D)) P = 1 then 1 else k P) (fun P hP => by
    by_cases h : ι (finPart D (x : AE D)) P = 1
    · rw [if_pos h, h, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
    · rw [if_neg h]
      exact ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  by_cases h : ι (finPart D (x : AE D)) P = 1
  · rw [if_pos h, map_one, Units.val_one]
  · rw [if_neg h]
    have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := (hS P hP).1
    rw [hv P] at a'
    have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
      show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
    show ((χ.loc P (Formalism.L2.Host.atFin P (k P)) : ℂˣ) : ℂ) = 1
    rw [hunr P h _ hun, Units.val_one]

end GlobalTheory.ChrOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDual
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem vacuum_unique_of_selfDual {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (Λ : Submodule R X)
    (hΛ : SelfDual γ Λ) (s : M) (hs : s ≠ 0) (hfix : Fixes W Λ s)
    (hspan : Submodule.span ℂ (Set.range fun x => W x s) = ⊤) (v : M) (hv : Fixes W Λ v) : ∃ c : ℂ, v = c • s := by
  have key : ∀ z : X, W z s = (γ (w • (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) : X))
      (z - Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)))⁻¹ • W (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)) s := by
    intro z
    set t : X := Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) with ht
    have hmem : z - t ∈ Λ := by
      rw [← Submodule.Quotient.eq]
      exact (Quotient.out_eq (Submodule.Quotient.mk z : X ⧸ Λ)).symm
    have h1 := h.comp t (z - t) s
    rw [hfix _ hmem, add_sub_cancel] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (h.ne_zero _ _), one_smul]
  have hli : LinearIndependent ℂ (fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    refine linearIndependent_of_simultaneous_eigen _ (fun q (a : Λ) => γ a (Quotient.out q)) (fun a : Λ => W a) ?_ ?_ ?_
    · intro q q' hq
      have hm : (Quotient.out q : X) - Quotient.out q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (Quotient.out q) = γ a (Quotient.out q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← Submodule.Quotient.eq] at hm
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      have e2 : (Submodule.Quotient.mk (Quotient.out q') : X ⧸ Λ) = q' := Quotient.out_eq q'
      rw [← e1, ← e2, hm]
    · intro a q
      rw [h.comm, hfix a a.2]
    · intro q h0
      have h1 := h.neg_comp (Quotient.out q) s
      rw [h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [key z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  have hb : ∀ q, b q = W (Quotient.out q) s := fun q => Module.Basis.mk_apply hli hsp q
  have hcoord : ∀ a ∈ Λ, ∀ q x, b.coord q (W a x) = γ a (Quotient.out q) * b.coord q x := by
    intro a ha q x
    have e : (b.coord q).comp (W a) = γ a (Quotient.out q) • b.coord q := by
      refine b.ext fun q' => ?_
      rw [LinearMap.comp_apply, hb, h.comm, hfix a ha, ← hb, LinearMap.smul_apply, map_smul, smul_eq_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hq
      · rw [hq]
      · simp
    exact LinearMap.congr_fun e x
  have h0 : (Quotient.out (0 : X ⧸ Λ) : X) ∈ Λ :=
    (Submodule.Quotient.mk_eq_zero Λ).1 (Quotient.out_eq (0 : X ⧸ Λ))
  have hb0 : b 0 = s := by rw [hb, hfix _ h0]
  have hvan : ∀ q : X ⧸ Λ, q ≠ 0 → b.repr v q = 0 := by
    intro q hq
    have hn : (Quotient.out q : X) ∉ Λ := fun hm => hq (by
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      rw [← e1]; exact (Submodule.Quotient.mk_eq_zero Λ).2 hm)
    rw [hΛ] at hn
    push_neg at hn
    obtain ⟨a, ha, hne⟩ := hn
    have hne' : γ a (Quotient.out q) ≠ 1 := fun e => hne (h.swap_eq_one e)
    have e := hcoord a ha q v
    rw [hv a ha, Module.Basis.coord_apply] at e
    have e2 : (γ a (Quotient.out q) - 1) * b.repr v q = 0 := by rw [sub_mul, ← e]; ring
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne')
  refine ⟨b.repr v 0, b.ext_elem fun q => ?_⟩
  rw [map_smul, ← hb0, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hq : (0 : X ⧸ Λ) = q
  · subst hq; simp
  · rw [if_neg hq, mul_zero, hvan q (Ne.symm hq)]

end GlobalTheory.SphTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResLoc

open GlobalTheory.IdemSupport Formalism.L2.JoinChr Formalism.L2.Host

theorem val_alg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem le_exp_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem locK_eq_of_tame {E : Type} [Field E] [NumberField E] (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (ht : χ.TameAt P) (k l : Eˣ) (hk : P.valuation E (k : E) = 1) (hl : P.valuation E (l : E) = 1)
    (h : P.valuation E ((k : E) - l) ≤ WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P l := by
  have h1 : χ.locK P (k * l⁻¹) = 1 := by
    refine ht (atFin P (k * l⁻¹)) ?_ ?_
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E)) = 1
      rw [val_alg, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hk, hl, inv_one, one_mul]
    · change Valued.v (algebraMap E (P.adicCompletion E) ((k * l⁻¹ : Eˣ) : E) - 1) ≤ _
      have e : ((k * l⁻¹ : Eˣ) : E) - 1 = ((k : E) - l) * (l : E)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ l.ne_zero]
      rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub, val_alg, e, map_mul, map_inv₀, hl, inv_one,
        mul_one]
      exact h
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

theorem exists_lift_lt_one {R T O K Γ : Type} [CommRing R] [CommRing T] [CommRing O] [CommRing K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (t : R →+* T) (ev : R →+* K) (S : Subring T) (o : O →+* S)
    (I : Ideal O) (hs : ∀ s : T, ∃ z, t z = s) (hint : ∀ z, t z ∈ S → v (ev z) ≤ 1)
    (hI : ∀ a ∈ I, ∃ z, t z = o a ∧ v (ev z) < 1) (s : S) (h : s ∈ I.map o) : ∃ z, t z = s ∧ v (ev z) < 1 := by
  refine Submodule.span_induction (p := fun (s : S) _ => ∃ z, t z = s ∧ v (ev z) < 1) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · exact ⟨0, map_zero _, by rw [map_zero, map_zero]; exact zero_lt_one⟩
  · rintro x y _ _ ⟨z, hz, h⟩ ⟨z', hz', h'⟩
    refine ⟨z + z', by rw [map_add, hz, hz']; rfl, ?_⟩
    rw [map_add]
    exact Valuation.map_add_lt _ h h'
  · rintro c x _ ⟨z, hz, h⟩
    obtain ⟨w, hw⟩ := hs c
    refine ⟨w * z, by rw [map_mul, hz, hw]; rfl, ?_⟩
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint w (hw ▸ c.2))) h

theorem map_eq_one_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 0)
    (hx : e * (x - 1) = x - 1) (hy : x = y * (1 + e * (k - 1))) : f y = 1 := by
  have h1 := congrArg f hx
  have h2 := congrArg f hy
  simp only [map_mul, map_add, map_sub, map_one, he, zero_mul, add_zero, mul_one] at h1 h2
  rw [← h2, ← sub_eq_zero, ← h1]

theorem map_eq_mul_of_supp {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {e x y k : R} (he : f e = 1)
    (hy : x = y * (1 + e * (k - 1))) : f x = f y * f k := by
  rw [hy]
  simp only [map_mul, map_add, map_sub, map_one, he]
  ring

theorem exists_units_quot {R : Type} [CommRing R] (x l : Rˣ) {r : R} (hl : (l : R) = r) :
    ∃ y : Rˣ, x = y * l ∧ (x : R) = y * r :=
  ⟨x * l⁻¹, (inv_mul_cancel_right x l).symm, by rw [← hl, ← Units.val_mul, inv_mul_cancel_right]⟩

variable {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

def evAt (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E :=
  (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) Q).comp Φ

theorem ev_sub (a b : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a - b) Q = Φ a Q - Φ b Q := by rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp D Φ) (a : D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (incA D a) Q = algebraMap D.host.E (Q.adicCompletion D.host.E) a := by rw [hΦ.inc]; rfl

theorem ev_eq_zero (hΦ : Comp D Φ) {z : AE D} (hz : finPart D z = 0) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ z Q = 0 := by
  let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
  have h0 : finPart D u = 0 := TensorProduct.zero_tmul _ _
  have h1 : infPart D u = 1 := rfl
  have h2 : z = u * z := by
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, h1, one_mul]
    · rw [RingHom.map_mul, hz, mul_zero]
  have h3 : Φ u Q = 0 := (hΦ.base _ Q).trans (map_zero _)
  rw [h2, ev_mul, h3, zero_mul]

theorem toEAf_surj (s : Datum.EAf D) : ∃ z : AE D, toEAf D z = s := by
  obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective s
  obtain ⟨z, -, hz⟩ := GlobalTheory.PlaceIdem.parts_surj D 0 y
  exact ⟨z, congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) hz⟩

theorem val_le_one (hΦ : Comp D Φ) {z : AE D} (hz : toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : Valued.v (Φ z Q) ≤ 1 :=
  (hΦ.int z).1 ((mem_intAE_iff _).2 hz) Q

theorem val_lt_one_of_mem (hΦ : Comp D Φ) (P : HeightOneSpectrum (𝓞 D.host.E))
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (hs : s ∈ idS D.host.F P.asIdeal) :
    ∀ z : AE D, toEAf D z = s → Valued.v (Φ z P) < 1 := by
  have key : ∃ z : AE D, toEAf D z = s ∧ Valued.v (Φ z P) < 1 := by
    refine exists_lift_lt_one Valued.v (toEAf D) (evAt Φ P) (Formalism.L2.Herm.intAf D.host.F D.host.E)
      (oToS D.host.F D.host.E) P.asIdeal toEAf_surj (fun z hz => val_le_one hΦ hz P) (fun a ha => ?_) s hs
    refine ⟨incA D a, rfl, ?_⟩
    change Valued.v (Φ (incA D a) P) < 1
    rw [ev_inc hΦ, val_alg]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) P a).2 ha
  obtain ⟨w, hw, h⟩ := key
  intro z hz
  have h1 : finPart D (z - w) = 0 := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    change toEAf D (z - w) = _
    rw [RingHom.map_sub, hz, hw, sub_self, map_zero]
  have h2 := ev_eq_zero hΦ h1 P
  rw [ev_sub, sub_eq_zero] at h2
  rwa [h2]

theorem exists_modulus (hΦ : Comp D Φ) (c : (AE D)ˣ →* Circle) (hc : Continuous c) :
    ∃ N : ℕ, 0 < N ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : (AE D)ˣ), infPart D (y : AE D) = 1 →
      (∀ Q, Q ≠ P → Φ (y : AE D) Q = 1) → Valued.v (Φ (y : AE D) P) = 1 →
      Valued.v (Φ (y : AE D) P - 1) ≤ P.valuation D.host.E (N : D.host.E) → c y = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N, hN, fun P y h0 h1 h2 h3 => ?_⟩
  have hN0 : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv : ∀ Q, Valued.v (Φ (y : AE D) Q) = 1 := fun Q => by
    by_cases hQ : Q = P
    · rw [hQ, h2]
    · rw [h1 Q hQ, map_one]
  have hv' : ∀ Q, Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := fun Q => by
    have : Valued.v (Φ (y : AE D) Q) * Valued.v (Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    rwa [hv, one_mul] at this
  refine hker y ⟨h0, (hΦ.int _).2 fun Q => (hv Q).le, (hΦ.int _).2 fun Q => (hv' Q).le⟩
    ⟨finPart D (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)), (hΦ.int _).2 fun Q => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_mul, val_alg, map_inv₀]
    by_cases hQ : Q = P
    · subst hQ
      exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0))).2 h3
    · rw [h1 Q hQ, sub_self, map_zero, mul_zero]
      exact zero_le
  · have e : (N : AE D) * (incA D (N : D.host.E)⁻¹ * ((y : AE D) - 1)) = (y : AE D) - 1 := by
      rw [← mul_assoc, ← map_natCast (incA D) N, ← RingHom.map_mul, mul_inv_cancel₀ hN0, RingHom.map_one, one_mul]
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, e, RingHom.map_sub, RingHom.map_one]

theorem val_sub_lt_one (hΦ : Comp D Φ) (P : Pl D.host.E) (x : AE D)
    (hi : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b : 𝓞 D.host.E)
    (hb : resS D.host.F P ⟨toEAf D x, hi⟩ = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (Φ x P - algebraMap D.host.E (P.adicCompletion D.host.E) (b : D.host.E)) < 1 := by
  have hm : (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
      idS D.host.F P.asIdeal := by
    have h0 : resS D.host.F P (⟨toEAf D (x : AE D), hi⟩ - oToS D.host.F D.host.E b) = 0 := by
      rw [RingHom.map_sub, resS_oToS, hb, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS D.host.F P.asIdeal)
      (cmpS_bij (F := D.host.F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  have h1 := val_lt_one_of_mem hΦ P _ hm ((x : AE D) - incA D b) (by rw [RingHom.map_sub]; rfl)
  rw [ev_sub, ev_inc hΦ] at h1
  exact h1

theorem resAt_of_tame (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (P : Pl D.host.E)
    (a : (kP P)ˣ →* ℂˣ) (ht : χ.TameAt P) (ha : IsRes χ P a) : GlobalTheory.StepLaw.ResAt c P a := by
  intro e he x hx hi u hu
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨d0, d1, d2⟩ := delta_of_isIdemAt hΦ he
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have hbP : b ∉ P.asIdeal := fun h => by
    have := P.isPrime
    exact u.ne_zero (hb.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hbv : P.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 hbP
  have h1 := val_sub_lt_one hΦ P x hi b (hu.symm.trans hb.symm)
  have h2 : Valued.v (Φ (x : AE D) P) = 1 := by
    rw [← hbv, ← val_alg]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [val_alg, hbv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (x : AE D) P) (fun h => by
    rw [h, map_zero] at h2
    exact zero_ne_one h2)
  rw [h2] at k1
  rw [← k1, mul_one] at k2 k3
  have hpl : IsPlIdem D e P := by
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨y, hy, hy'⟩ := exists_units_quot x l hl
  have hyP : Φ (x : AE D) P = Φ (y : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hy'
  have hcy : c y = 1 := by
    refine hker P y (map_eq_one_of_supp (infPart D) d0 hx hy')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hx hy') ?_ ?_
    · rwa [hyP, map_mul, val_alg, ← k1, mul_one] at h2
    · rwa [hyP, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcx : c x = c l := by rw [hy, map_mul, hcy, one_mul]
  rw [ha b (Units.mk0 _ hb0) u rfl hb.symm, hcx, hc.2 P e hpl k l hl,
    locK_eq_of_tame χ P ht k (Units.mk0 _ hb0) k1.symm hbv]
  have e5 : algebraMap D.host.E (P.adicCompletion D.host.E) ((k : D.host.E) - (b : D.host.E)) =
      (Φ (x : AE D) P - algebraMap D.host.E _ (b : D.host.E)) - (Φ (x : AE D) P - algebraMap D.host.E _ (k : D.host.E)) := by
    rw [map_sub]
    ring
  rw [Units.val_mk0, ← val_alg, e5]
  exact Valuation.map_sub_le _ (le_exp_of_lt_one h1) k3

theorem resAt_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  intro D c χ hc P
  refine ⟨fun a => resAt_of_tame c χ hc P a, fun h => resAt_of_tame c χ hc P 1 (fun x hx _ => h x hx) ?_⟩
  intro b k u hk hu
  refine (h (atFin P k) ?_).symm
  change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
  rw [val_alg, hk]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := b)).2 fun hb => ?_
  have := P.isPrime
  exact u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 hb))

end GlobalTheory.ResLoc

end
end

