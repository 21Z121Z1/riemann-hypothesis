import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0049
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0050
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdFlagJ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem flag_of_rel {K H : Type} [Field K] [Group H] {n : ℕ} (r : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (h0 : ∀ g : Fin n → H, (List.ofFn fun i => ((r (g i) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      algebraMap K _ ((ψ i (g i) : Kˣ) : K)).prod = 0)
    (hch : ∀ t, (W.mat r t).charpoly = ∏ i, (X - C ((ψ i t : Kˣ) : K)))
    (s : H) (hs : Function.Injective fun i => ψ i s) : W.HasFlag r ψ := by
  classical
  let z : MonoidAlgebra K H := MonoidAlgebra.of K H s
  have hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K) := fun i => by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s := by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hext := AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r)
    (fun i => (Units.coeHom K).comp (ψ i)) h0
  have hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z -
      MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z) := fun i j hij => by
    rw [hlz, hlz]
    exact (sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit
  obtain ⟨hc, hlow, hdiag⟩ := AlgebraTools.lag_triangular
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz
  have hne := AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by
      rw [hPz, hch, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hlz]
      simp)
  obtain ⟨g, hg⟩ := AlgebraTools.coi_conj_single _ hc hne
  refine ⟨g, fun t => ?_⟩
  set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf
  have ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b,
      (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b := fun M a b => by
    simp
  have key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b := by
    intro a b
    rw [← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h := hlow (MonoidAlgebra.of K H t) i j hji
    rw [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0 := h
    rw [key, h']
    simp
  · have h := hdiag (MonoidAlgebra.of K H t) i
    simp only [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i := h
    rw [key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]
    simp
private theorem chi_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp
private theorem descend {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Ws.Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Ws.Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, chi_single]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn] at e
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]
theorem UpperTheory.V.Z.Ord.flagJ_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → FlagJ := by
  intro H l _ L Ω _ _ _ _ _ _ s n V c r B Λ J hJ x h ρ hJx hA hx hirr v
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · exact absurd (Subsingleton.elim _ _) hirr.1
    · exact h0
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Ws.Eb.Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => by
    rcases hirr.2.2 N le_top fun g v hv => hN g v hv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := descend x.D V.pr hs ρ hn hF hx
  obtain ⟨hO, -⟩ := Ws.Eb.relKill B x ρ₀ hfull hD
  obtain ⟨g₀, hg₀⟩ := _root_.UpperTheory.V.Th.Nm.regular_arithmetic_hida_of_literal_automorphy H s h v (x.psi v) hA.1 (hA.2 v)
  refine flag_of_rel _ (x.psi v) (hO v) (fun t => ?_) g₀ hg₀
  let xb : B.B ⧸ J →+* Qbar l := Ideal.Quotient.lift J (x : B.B →+* Qbar l) fun a ha => hJx ha
  have e0 : xb.comp (Ideal.Quotient.mk J) = (x : B.B →+* Qbar l) := RingHom.ext fun a => rfl
  have e1 : (B.DD J).map xb = W.GDet.ofRep (W.mat ρ₀) := by
    have h1 : (B.DD J).map xb = B.u.D.map (xb.comp (Ideal.Quotient.mk J)) := (CA.d_gmap B.u.D).2.1 _ _
    rw [h1, e0]
    exact hD
  have e2 := (AlgebraTools.Det.mapApi (B.DD J) xb).1 (MonoidAlgebra.single (V.frame.φ v t) 1)
  rw [MonoidAlgebra.mapRingHom_single, map_one, e1, (AlgebraTools.Det.repApi _).2.1] at e2
  refine e2.trans ((congrArg (Polynomial.map xb) (hJ.O1 v t)).trans ?_)
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdOrdScal
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem char_at {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    {F : M} (hne : F ≠ 0) (h : ∀ t, ∃ a : ℂ, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t)
        rw [map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t => by simpa [χ] using ha t⟩
private theorem uOp_at {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  intro F hF
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]
private theorem Uc_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))
private theorem local_exp (hJ : OrdJac) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    {F : M} (hFY : F ∈ Y) (hF0 : F ≠ 0) (e : ℕ) (f : Fin n → Uo k → ℂ)
    (hN : F ∈ fixd ρ (glIwa k n).N) (hNm : F ∈ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (a : ℕ → ℂ)
    (ha : ∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp ρ (al k n (j + 1)) F = a (j + 1) • F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient σ.ρ (PS ω) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧ ∀ j : Fin n, psEig ω (j + 1) = a (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_at (ρ.comp (glIwa k n).T.subtype) hF0 fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF0 ((hφ (eT k n i y)).symm.trans (hT i y))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  obtain ⟨p, hp, hp0⟩ := isoSep hσ hFY hF0
  have hpe : p F ∈ (glIwa k n).eig σ.ρ e φ :=
    ⟨fun u hu => by rw [← hp u F hFY, hN u hu], fun u hu => by rw [← hp u F hFY, hNm u hu],
      fun t => (hp _ F hFY).symm.trans ((congrArg p (hφ t)).trans (map_smul p _ _))⟩
  obtain ⟨ω, h1, h2, h3, h4⟩ := hJ k n σ.V σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one])) (p F) hpe hp0 a fun j =>
      ⟨(ha j).1, (uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n (j + 1)) F fun u _ => hp _ F hFY).symm.trans
        ((congrArg p (ha j).2).trans (map_smul p _ _))⟩
  exact ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], h4⟩
theorem UpperTheory.V.Z.Ord.ordinary_scalar_of_literal_automorphy_n : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.OrdScalAlt := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K e he F hF hF0 v b hb
  classical
  have hN : F ∈ fixd (H.atV d v) (glIwa _ n).N := fun u hu =>
    hF.2.1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : F ∈ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun u hu =>
    hF.2.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ i y, H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun i y => by
    have := hF.2.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ j : Fin n, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun j =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·)
      (uOp_at (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n) (H.X.rpF ℂ d H.m) v (al_mem _ n (j + 1)) F hF.2.1.1.2)
  have hl : ∀ j : Fin n, H.lowVal ι lam v (j + 1) ≠ 0 := fun j h0 => by
    have := (hb j).2
    rw [hop j, h0, inv_zero, zero_smul] at this
    exact smul_ne_zero (hb j).1 hF0 this.symm
  let a : ℕ → ℂ := fun m => H.lowVal ι lam v m * (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0)
  have ha : ∀ j : Fin n, a (j + 1) = H.lowVal ι lam v (j + 1) * b j := fun j => by
    have h : (j : ℕ) + 1 - 1 < n := by simpa using j.2
    simp only [a, dif_pos h]
    congr 2
  obtain ⟨ω, h1, h2, h3, h4⟩ := local_exp (_root_.UpperTheory.V.Z.Ord.ordinary_jacquet_of_literal_automorphy_n hLit) (H.atV d v) (Y.σl v) (Y.isoL v) hF.1 hF0 e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) hN hNm hT
    (fun i y hy => by rw [hsp.triv v i y (Uc_le _ (by omega) hy), map_one]) a fun j =>
      ⟨by rw [ha j]; exact mul_ne_zero (hl j) (hb j).1, by
        have h := (hop j).symm.trans (hb j).2
        rw [inv_smul_eq_iff₀ (hl j), smul_smul] at h
        rw [ha j]
        exact h⟩
  exact ⟨ω, h1, h2, h3, fun j => by rw [h4 j, ha j, inv_mul_cancel_left₀ (hl j)]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAtSame
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem ev_of_gen {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (μ a : ℂ) (F : M) (hF : F ≠ 0)
    (h : F ∈ T.maxGenEigenspace μ) (ha : T F = a • F) : a = μ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T μ F).1 h
  have h1 : ∀ j : ℕ, ((T - μ • 1) ^ j) F = (a - μ) ^ j • F := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, ha]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
      rw [← sub_smul, smul_smul, pow_succ]
  rw [h1 k] at hk
  have h2 := (smul_eq_zero.1 hk).resolve_right hF
  by_contra hne
  exact pow_ne_zero k (sub_ne_zero.2 hne) h2
private theorem sat_eq (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ) (a a' : ℕ → ℂ) (haa : ∀ j ≤ n, a j = a' j)
    (h : ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a)
    (h' : ((UpperTheory.V.Af.algSat n q B').map fun b => X - C b).prod = heckePol n q a') : B = B' := by
  have hp : heckePol n q a = heckePol n q a' := by
    rw [UpperTheory.V.Hi.heckePol, UpperTheory.V.Hi.heckePol]
    exact Finset.sum_congr rfl fun j hj => by rw [haa j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have hr : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B' := by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (UpperTheory.V.Af.algSat n q B), h, hp, ← h',
      Polynomial.roots_multiset_prod_X_sub_C]
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  unfold UpperTheory.V.Af.algSat at hr
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map] at hr
  exact Multiset.map_injective (fun x y hxy => Units.ext (mul_left_cancel₀ hc hxy)) hr
private theorem mem_gen {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (b : ℕ) (ev : H.Op → ℂ) (i : H.Op)
    (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ zPart H θ ι x lam ξ K b ev) : F ∈ (H.opC ι lam d i).maxGenEigenspace (ev i) :=
  (Submodule.mem_iInf _).1 hF.2 i
private theorem vals (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (Z : Submodule ℂ (Fin m → (hset Q τ₀).X.Fn ℂ d))
    (ev : (hset Q τ₀).Op → ℂ) (hZ : ∀ i, ∀ F ∈ Z, F ∈ ((hset Q τ₀).opC ι lam d i).maxGenEigenspace (ev i))
    (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ) (hY : YOf Q ι τ₀ e ξ σ ⊓ Z ≠ ⊥)
    (w : (hset Q τ₀).Wp) (τ : SmIrr (GLw n w.1)) (hτ : Cp σ w.1 τ) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w.1 τ.ρ B) :
    ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j : Fin n, a (j + 1) = ev (.inl (w, j))) ∧
      ((UpperTheory.V.Af.algSat n (normV w.1) B).map fun b => X - C b).prod = heckePol n (normV w.1) a := by
  obtain ⟨-, a, ha0, ha, hp⟩ := satT L n w.1 τ B hB
  refine ⟨a, ha0, fun j => ?_, hp⟩
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  have hAx : (hset Q τ₀).Ax := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  have h1 := partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w.1 w.2.1 w.2.2 τ hτ (j + 1) _ (ha (j + 1)) F hF.1
  exact ev_of_gen _ _ _ F hF0 (hZ (.inl (w, j)) F hF.2) h1
theorem atSame_alt : _root_.UpperTheory.V.Z.J.D.AtSameAlt := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev σ σ' hσ hσ' h1 h2 π hπ
  have hZ := fun i F hF => mem_gen (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev i F hF
  have hY' : YOf Q ι τ₀ e ξ σ' ≠ ⊥ := fun h => h2 (eq_bot_iff.2 (inf_le_left.trans h.le))
  have hU := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hY'
  have hfin : ∀ᶠ w : Plc L in cofinite, w.under (𝓞 (Lp L)) ∉ V.S' :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually V.fin.compl_mem_cofinite
  refine (hπ.and hfin).mono ?_
  rintro w ⟨hw, hS⟩ hsp
  obtain ⟨τ, B, hτ, hB, hs⟩ := hw hsp
  obtain ⟨τ', -, h1', h2'⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ', hσ'⟩ w hsp
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ'.smooth τ'.irred (h2'.1 (hU w hS))
  let w' : (hset Q τ₀).Wp := ⟨w, hS, hsp⟩
  obtain ⟨a, a0, ha, hp⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ hσ h1 w' τ hτ B hB
  obtain ⟨a', a0', ha', hp'⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ' hσ' h2 w' τ' h1' B' hB'
  have hBB := sat_eq n (normV w) (GlobalTheory.LFun.qV_ne_zero w) B B' a a' (fun j hj => by
    rcases j with _ | j
    · rw [a0, a0']
    · have := ha ⟨j, hj⟩
      have h' := ha' ⟨j, hj⟩
      exact this.trans h'.symm) hp hp'
  subst hBB
  exact ⟨τ', B, h1', hB', hs⟩
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSphSame
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem lat {α : Type*} [Lattice α] {Y B f z E : α} (h1 : Y ≤ B) (h2 : Y ≤ f) (h3 : Y ≤ E) :
    Y ⊓ (B ⊓ f ⊓ z ⊓ E) = Y ⊓ z :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (le_inf inf_le_left (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_left.trans h2)) inf_le_right)
      (inf_le_left.trans h3)))
private theorem eig_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {a b : ℂ} {F : M} (h0 : F ≠ 0)
    (hT : T F = a • F) (hF : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hF
  have h1 : (T - b • (1 : Module.End ℂ M)) F = (a - b) • F := by
    simp [hT, sub_smul]
  have h : ∀ i : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ i) F = (a - b) ^ i • F := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [h k] at hk
  by_contra hne
  exact smul_ne_zero (pow_ne_zero k (sub_ne_zero.2 hne)) h0 hk
private theorem eig_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {b : ℂ} {F : M}
    (hT : T F = b • F) : F ∈ T.maxGenEigenspace b :=
  (Module.End.mem_maxGenEigenspace T b F).2 ⟨1, by simp [hT]⟩
private theorem eig_le {M I : Type*} [AddCommGroup M] [Module ℂ M] (T : I → Module.End ℂ M) (ev : I → ℂ) (i : I) (a : ℂ)
    (O Y Y' : Submodule ℂ M) (hne : Y ⊓ (O ⊓ ⨅ i, (T i).maxGenEigenspace (ev i)) ≠ ⊥)
    (h1 : ∀ F ∈ Y, T i F = a • F) (h2 : ∀ F ∈ Y', T i F = a • F) : Y' ≤ (T i).maxGenEigenspace (ev i) := by
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hFe : F ∈ (T i).maxGenEigenspace (ev i) :=
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).2).2 i
  have hae : a = ev i := eig_eq _ hF0 (h1 F (Submodule.mem_inf.1 hF).1) hFe
  intro F' hF'
  exact eig_mem _ (hae ▸ h2 F' hF')
private theorem scalar (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)) (j : ℕ) :
    ∃ a : ℂ, ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v := by
  by_cases h : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w n)
  · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred h
    obtain ⟨-, a, -, ha, -⟩ := UpperTheory.V.Hi.satT L n w τ B hB
    exact ⟨a j, ha j⟩
  · refine ⟨0, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra h0
      rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
      exact h ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩)
    simp [hv0]
theorem spherical_same_of_z_eq : ZEq → _root_.UpperTheory.V.Z.J.D.SphSameAlt := by
  intro hZ hLit l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev hev σ σ' hσ hσ' hcp hne
  have hAx := _root_.UpperTheory.V.Hi.axU_s hLit l L Ω s n hn V Q c m τ₀
  have hYB : YOf Q ι τ₀ e ξ σ' ≤ (hset Q τ₀).Big ι ξ := inf_le_left
  rw [hZ L Ω l n c (hset Q τ₀) hAx A θ hWt ι x lam d ξ c0 sp hSp K ev hev]
  refine lat hYB ?_ ?_
  · haveI : IsEmpty (hset Q τ₀).Q := ⟨fun q => Q.notS q (by
      have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
        rw [Q.range]
        exact Or.inr ⟨q, rfl⟩
      rwa [hV] at h)⟩
    have hl : (hset Q τ₀).lev K = (hset Q τ₀).UQ := by
      simp only [HSet.lev, iSup_of_empty]
      exact sup_bot_eq _
    rw [hl]
    exact hYB.trans inf_le_right
  · refine le_iInf fun p => ?_
    obtain ⟨τ, h1, h2⟩ := hcp p.1.1 p.1.2.2
    obtain ⟨a, ha⟩ := scalar L n p.1.1 τ ((p.2 : ℕ) + 1)
    have hs := fun (σ₁ : Submodule ℂ (UA L n → ℂ)) (hσ₁ : IsAutRepU σ₁) (hτ₁ : Cp σ₁ p.1.1 τ) =>
      UpperTheory.V.Hi.partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ₁ hσ₁ hAx p.1.1 p.1.2.1 p.1.2.2 τ hτ₁ _ a ha
    exact eig_le ((hset Q τ₀).opC ι lam d) ev (.inl p) a ((hset Q τ₀).OrdAt θ ι x.toRingHom lam ξ K c0) _ _ hne
      (hs σ hσ h1) (hs σ' hσ' h2)
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinPairs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AAcross2Alt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → RowT → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ r : G ℚ Ω →* GL (Fin n) (Qbar l), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v) →
    Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsAlgChar ι θ ∧ DualTw r θ) → IneAb r → Flagged r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) →
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → WitAQ ι r
variable {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
end UpperTheory.V.Z.Win
end
end
end

