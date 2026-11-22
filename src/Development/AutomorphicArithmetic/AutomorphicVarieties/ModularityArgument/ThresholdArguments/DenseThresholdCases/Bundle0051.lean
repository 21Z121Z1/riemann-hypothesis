import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAwayW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V
private theorem split_of_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {p : Polynomial K} (a b : K'ˣ)
    (h : p.map e.toRingHom = (Polynomial.X - Polynomial.C (a : K')) * (Polynomial.X - Polynomial.C (b : K'))) :
    ∃ a' b' : Kˣ, e a' = a ∧ e b' = b ∧
      p = (Polynomial.X - Polynomial.C (a' : K)) * (Polynomial.X - Polynomial.C (b' : K)) := by
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom a, Units.map e.symm.toRingHom.toMonoidHom b, ?_, ?_, ?_⟩
  · simp
  · simp
  · apply Polynomial.map_injective e.toRingHom e.injective
    rw [h]
    simp
private theorem roots3 {K : Type} [Field K] {p : Polynomial K} {a b c : K}
    (h : p = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c)) :
    p.IsRoot a ∧ p.IsRoot b ∧ p.IsRoot c := by
  subst h
  simp
private theorem link_false {l : ℕ} [Fact l.Prime] {x : Matrix.GeneralLinearGroup (Fin 3) (Qbar l)} {Q : ℕ} (hn : NoLink x Q) (c : Qbar l) (h0 : c ≠ 0)
    (r0 : x.val.charpoly.IsRoot c)
    (r1 : x.val.charpoly.IsRoot 1)
    (r2 : x.val.charpoly.IsRoot c⁻¹)
    {j : ℕ} (hj : j = 1 ∨ j = 2) (hQ : c ^ j = Q ∨ c ^ j * Q = 1) : False := by
  rcases hj with rfl | rfl <;> rcases hQ with e | e
  · exact hn _ _ r0 r1 1 le_rfl (by simpa using e)
  · exact hn _ _ r1 r0 1 le_rfl (by
      simp only [pow_one] at e ⊢
      rw [mul_comm (Q : Qbar l), e])
  · exact hn _ _ r0 r2 1 le_rfl (by
      rw [pow_one, pow_one, ← e]
      field_simp)
  · exact hn _ _ r2 r0 1 le_rfl (by
      rw [pow_one, pow_one]
      exact inv_eq_of_mul_eq_one_right (by linear_combination e))
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime]
private theorem adjoint_inertia_image_finite (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin 2) (Qbar l)}
    {y : WD h} (hx : IsWDOf ι r y) (hy : y.mono0) : (ad0 r '' (Ine (F := L) A : Set (G L Ω))).Finite := by
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  have hN0 : N = 0 := (hN.weilDeligneParam_monodromy_eq_zero_iff hl ht ι).1 (hw ▸ hy)
  subst hN0
  obtain ⟨-, U, hU, H⟩ := hN
  have hu : ∀ σ ∈ U, ad0 r (σ : G L Ω) = 1 := fun σ hσ => by
    have h1 : r (σ : G L Ω) = 1 := Units.ext (by rw [H σ hσ]; simp)
    apply Units.ext
    rw [ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1]
    simp
  haveI := compactSpace_Ine (E := L) A
  let f := (ad0 r).comp (Ine (F := L) A).subtype
  haveI : Finite (Ine (F := L) A ⧸ f.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono (H₁ := U) (fun x hx => hu x hx) hU)
  haveI : Finite f.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv
  refine (Set.toFinite (f.range : Set (GL (Fin 3) (Qbar l)))).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩
end
end UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V in
theorem UpperTheory.V.Z.Sym.W.away_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.AwayWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι r hr hU w hl τ hg hT
  obtain ⟨ψ, hψ, ⟨e⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.principal_series_of_statement_w P.litN L 2 w τ hT
  refine ⟨ψ, hψ, ⟨e⟩, ?_⟩
  intro j hj ε hε hlk
  obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN h
  have gd : Gd (rc (algNorm τ)) := Gu.plainGd L Ω A w h rc hrc 2 τ hT
  have hx : IsWDOf ι r (rc (algNorm τ)) := ((hg A h rc hrc).1 hl).isWDOf gd
  obtain ⟨a, ha, -⟩ := id hrc
  obtain ⟨s, j', hj', hs, hn⟩ := hU w hl A h (adjoint_inertia_image_finite hl hx gd.2)
  have hact : ActsAs A (normV w) s j' 0 := by
    simp only [ActsAs, pow_zero, pow_one]
    exact hs
  let S : Weil h := ⟨s, j', 0, hact⟩
  have hd : deg S = (j' : ℤ) := by simpa using deg_eq (σ := S) hact
  have hcp := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P L Ω l ι 2 r w hl A h a ha τ hg hT ψ hψ
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective) S
  rw [psPol, Fin.prod_univ_two] at hcp
  obtain ⟨a', b', ea, eb, hab⟩ := split_of_map ι _ _ hcp
  have hc := (ad0Facts l (G L Ω) r).2.2.2.2.1 s a' b' hab
  obtain ⟨r0, r1, r2⟩ := roots3 hc
  have hci : ((b' / a' : (Qbar l)ˣ) : Qbar l) = (((a' / b' : (Qbar l)ˣ) : Qbar l))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val, inv_div]
  rw [hci] at r2
  refine link_false hn _ (Units.ne_zero _) r0 r1 r2 hj ?_
  have hc' : ι ((a' / b' : (Qbar l)ˣ) : Qbar l) = ((ψ 0 (a S) / ψ 1 (a S) : ℂˣ) : ℂ) := by
    rw [Units.val_div_eq_div_val, map_div₀, ea, eb, ← Units.val_div_eq_div_val, mul_div_mul_right_eq_div]
  have hv : (ψ 0 (a S) / ψ 1 (a S)) ^ j = absPow (w.adicCompletion L) (ε : ℂ) (a S) := by
    rw [← hlk]
    rfl
  have hz : ι (((a' / b' : (Qbar l)ˣ) : Qbar l) ^ j) = ((absPow (w.adicCompletion L) (ε : ℂ) (a S) : ℂˣ) : ℂ) := by
    rw [map_pow, hc', ← Units.val_pow_eq_pow_val, hv]
  rcases hε with rfl | rfl
  · left
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (1 : ℝ) S
    rw [hd] at h1
    rw [hz, map_natCast]
    simpa using h1
  · right
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (-1 : ℝ) S
    rw [hd] at h1
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
    rw [map_mul, hz, map_natCast, map_one]
    have h2 : ((absPow (w.adicCompletion L) (((-1 : ℤ) : ℂ)) (a S) : ℂˣ) : ℂ) = (((normV w : ℕ) : ℂ)⁻¹) ^ j' := by
      simpa [Complex.cpow_neg_one] using h1
    rw [h2]
    push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreUp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem up_list {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) : (s.map fun v => Pi.mulSingle v (g v)).prod w = if w ∈ s then g w else 1 := by
  induction s with
  | nil => simp
  | cons v s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hs.2]
    by_cases h : w = v
    · subst h; simp [hs.1]
    · simp [h]
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
private theorem up_VV (d : ℕ) (v v' : H.V) (h : v ≠ v') (g g') (F) :
    H.atV d v g (H.atV d v' g' F) = H.atV d v' g' (H.atV d v g F) := by
  classical
  change (H.X.rpF ℂ d H.m (Pi.mulSingle v g) * H.X.rpF ℂ d H.m (Pi.mulSingle v' g')) F =
    (H.X.rpF ℂ d H.m (Pi.mulSingle v' g') * H.X.rpF ℂ d H.m (Pi.mulSingle v g)) F
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) h g g').eq]
private theorem up_PA (d : ℕ) (g u) (F) :
    H.X.rpF ℂ d H.m g (H.X.raF d (H.τC ι) u F) = H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m g F) := by
  funext i x k
  change (H.X.ra (H.τC ι) u (fun y j => F j y k) (x * (1, g))) i =
    H.X.ra (H.τC ι) u (fun y j => F j (y * (1, g)) k) x i
  rw [Frame.ra_apply, Frame.ra_apply]
  simp [mul_assoc]
private theorem up_vec (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hH : H.Ax) {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ}
    (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (hK : ∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (hω : ∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) (e : ℕ)
    (he : ∀ v i, ∀ y ∈ Uc _ (e + 1), ω v i y = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v)) :
    ∃ F ∈ Y.Y, F ≠ 0 ∧ (∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) ∧
      ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q) := by
  refine Exists.imp (fun F h => ⟨h.1, h.2.1, fun v => h.2.2 (.inl v), fun q => h.2.2 (.inr q)⟩) (Up.meet (I := H.V ⊕ H.Q)
    (Sum.elim (fun v => Set.range (H.atV d v)) fun q => Set.range (H.atW ι d (H.wq q)))
    (Sum.elim (fun v => Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) fun q => fixd (H.atW ι d (H.wq q)) (K.1 q))
    Y.Y Y.ne ?_ ?_ ?_)
  · rintro (v | q) _ ⟨g, rfl⟩
    · exact Up.isoStab (Y.isoL v) g
    · exact Up.isoStab (Y.isoQ q) g
  · rintro (v | q) (v' | q') hne _ ⟨g, rfl⟩
    · exact Up.ordMap _ _ _ (fun g' F => up_VV H d v' v (fun h => hne (by rw [h])) g g' F) _ _ _
    · exact Up.ordMap _ _ _ (fun g' F => (up_PA H ι d _ _ F).symm) _ _ _
    · exact Up.fixMap (H.atW ι d (H.wq q)) (H.atW ι d (H.wq q)) _ (fun g' F => up_PA H ι d _ _ F) _
    · refine Up.fixMap _ _ _ (fun g' F => ?_) _
      change (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F = (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F
      rw [← map_mul, ← map_mul]
      exact congrArg (fun u => H.X.raF d (H.τC ι) u F) (hH.Q_Q q q' (fun h => hne (by rw [h])) g' g).eq.symm
  · rintro (v | q) Z hZ hne hst
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoL v) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := _root_.UpperTheory.V.Hi.exists_ne_zero_mem_eig_uOp_eq_psEig_smul_of_equiv_ps hL _ n _ (Y.σl v).ρ (ω v) (hω v) e (he v) (φ v) (hφ v)
      refine (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, ?_⟩, fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
      exact Up.ordMap _ _ p hp1 _ _ _ u ((Up.mem_ordC _ _ _ _ _).2 ⟨hu1, hu3⟩)
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoQ q) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2⟩ := (Submodule.ne_bot_iff _).1 (hK q)
      exact (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, Up.fixMap _ _ p hp1 _ u hu1⟩,
        fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
private theorem up_ord {A : Type} [CommRing A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l)
    {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} (K : H.Lev)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (e : ℕ)
    (hω : ∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x lam v i u) = 1)
    (hn : ∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v))
    (F : Fin H.m → H.X.Fn ℂ d) (hB : F ∈ H.Big ι ξ) (hV : ∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v)))
    (hQ : ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q)) :
    F ∈ H.OrdAt θ ι x lam ξ K e ∧ ∀ v (j : Fin n),
      H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  classical
  simp only [Up.mem_ordC] at hV
  let I := fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n
  have hN : F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N := Up.fixPi _ (fun v => (I v).N) F fun v => (hV v).1.1
  have hNm : F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) := Up.fixPi _ (fun v => (I v).Nm e) F fun v => (hV v).1.2.1
  have hlev : F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) := by
    intro u hu
    let St : Subgroup H.X.Ub :=
      (MulAction.stabilizer (Module.End ℂ (Fin H.m → H.X.Fn ℂ d))ˣ F).comap (H.X.raF d (H.τC ι)).toHomUnits
    have : H.lev K ≤ St := sup_le (fun u hu => hB.2 u hu) (iSup_le fun q => by
      rintro _ ⟨g, hg, rfl⟩
      exact hQ q g hg)
    exact this hu
  have hCl : F ∈ H.ClAt θ ι x lam ξ K e := by
    refine ⟨⟨⟨⟨hB, hlev⟩, hN⟩, hNm⟩, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    have h1 := (hV v).1.2.2 (eT _ n i y)
    rw [hφ v i y, inv_inv, eq_inv_of_mul_eq_one_left (hω v i y)] at h1
    exact h1
  have hz : ∀ v, (I v).uOp (H.atV d v) (I v).z F = ((List.range n).map (psEig (ω v))).prod • F := by
    intro v
    have h1 := (glBridge ((H.Sl v).adicCompletion L) n _ (H.atV d v)).2.2.2.2.2.2.2.2.1
    have h2 := (Up.uOpList (I v) (H.atV d v) F (hV v).1.1 (al _ n) (psEig (ω v)) (List.range n)
      fun j hj => ⟨al_mem _ n j, (hV v).2 j (List.mem_range.1 hj).le⟩).2
    rwa [← h1] at h2
  have hZ := (Up.uOpList (piIwa I) (H.X.rpF ℂ d H.m) F hN (fun v => Pi.mulSingle v (I v).z)
    (fun v => ((List.range n).map (psEig (ω v))).prod) Finset.univ.toList
    fun v _ => ⟨Up.singleP I v _ (I v).z_mem, (Up.uOpPi I _ v _ (I v).z_mem F hN).trans (hz v)⟩).2
  have hzz : (Finset.univ.toList.map fun v => (Pi.mulSingle v (I v).z : GV n H.Sl)).prod = H.X.I.z := by
    funext w
    rw [up_list (fun v => (I v).z) w _ (Finset.nodup_toList _), if_pos (by simp)]
    rfl
  rw [hzz, Finset.prod_map_toList] at hZ
  have hl : ∀ v, ((List.range n).map (psEig (ω v))).prod = ∏ j ∈ Finset.range n, psEig (ω v) j := fun v => rfl
  simp only [hl] at hZ
  refine ⟨?_, fun v j => ?_⟩
  · refine Submodule.mem_iSup_of_mem
      ⟨∏ v, ∏ j ∈ Finset.range n, (H.lowVal ι lam v j)⁻¹ * psEig (ω v) j, ?_⟩ ⟨hCl, ?_⟩
    · rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun j hj => ?_
      rcases j with _ | j
      · simp [HSet.lowVal, psEig]
      · exact hn v ⟨j, by have := Finset.mem_range.1 hj; omega⟩
    · refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 ?_)
      change (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) H.X.I.z F = _
      rw [hZ, smul_smul]
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  · change (H.lowVal ι lam v (j + 1))⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) (Pi.mulSingle v (al _ n (j + 1))) F = _
    rw [Up.uOpPi I _ v _ (al_mem _ n _) F hN, ← smul_smul]
    exact congrArg _ ((hV v).2 _ j.2)
end
theorem UpperTheory.V.Hi.coreUp_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev), (∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥) → ∀ ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) → (∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x.toRingHom lam v i u) = 1) → ∀ a : H.Op → c.O, (∀ w (j : Fin n), ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, j)))‖ < 1) → (∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧ ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) - algebraMap c.O (Qbar l) (a (.inr (v, j)))‖ < 1) → ∀ [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ ∧ ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ (∀ w (j : Fin n), ι (y (H.gen θ a K (.inl (w, j)))) = Y.a w (j + 1)) ∧ ∀ v (j : Fin n), ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1) := by
  intro hL L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K hK ω hω1 hω2 a ha1 ha2 hFact
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  choose φ hφ using fun v => Up.exInv (ω v)
  obtain ⟨F, hF, h0, hV, hQ⟩ := up_vec H ι hL hH Y K hK ω hω1 c0 (fun v i y hy => by
    have h := hω2 v i ⟨y, Up.Uc_le _ hy⟩
    rw [hsp.triv v i _ hy, map_one, mul_one] at h
    exact Units.ext h) φ hφ
  obtain ⟨hO, hU⟩ := up_ord H ι θ x.toRingHom K ω c0 hω2 (fun v j => (ha2 v j).1) φ hφ F (Y.le hF) hV hQ
  rw [← hsp.span K c0 le_rfl] at hO
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hFact
  obtain ⟨hne, y, hy1, hy2⟩ := Up.eigPt (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) F hO h0
    (Sum.elim (fun p => Y.a p.1 (p.2 + 1)) fun p => (H.lowVal ι lam p.1 (p.2 + 1))⁻¹ * psEig (ω p.1) (p.2 + 1))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact Y.sph w _ F hF
      · exact hU v j)
    (fun i => algebraMap c.O A (a i))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact (x.commutes _).symm ▸ ha1 w j
      · exact (x.commutes _).symm ▸ (ha2 v j).2)
  refine ⟨hne, ⟨y, fun o => ?_⟩, RingHom.ext hy1, fun w j => hy2 (.inl (w, j)),
    fun v j => hy2 (.inr (v, j))⟩
  refine Eq.trans (congrArg y ?_) ((hy1 _).trans (x.commutes o))
  exact Subtype.ext (LinearMap.ext fun f => (algebraMap_smul A o f).symm)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGoodW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W.GoodWeilCharpoly
private theorem one_of_sq {a b : ℂ} (h : (X - 1 : ℂ[X]) ^ 2 = (X - C a) * (X - C b)) : a = 1 ∧ b = 1 := by
  have ha := congrArg (eval a) h
  have hb := congrArg (eval b) h
  simp only [eval_pow, eval_sub, eval_X, eval_one, eval_mul, eval_C, sub_self, zero_mul, mul_zero] at ha hb
  exact ⟨sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 ha), sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hb)⟩
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem absPow_int_val (m : ℤ) (x : kˣ) : (absPow k (m : ℂ) x : ℂ) = (absPow k 1 x : ℂ) ^ m := by
  rw [val_absPow, val_absPow, Complex.cpow_intCast, Complex.cpow_one]
end Loc
end UpperTheory.V.Z.Sym.W.GoodWeilCharpoly
theorem UpperTheory.V.Z.Sym.W.good_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.GoodWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι r w hlw hunr ⟨s, ⟨A, hA, hF⟩, hs⟩ τ hτ hPT
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN hA
  obtain ⟨a, ha, -⟩ := hrc
  obtain ⟨ψ, hψs, ⟨e⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.principal_series_of_statement_w P.litN L 2 w τ hPT
  have hsub : IsSubquotient τ.ρ (prinSeries ψ) := by
    exact IsSubquotient.of_injective e.toIntertwiningMap e.toLinearEquiv.injective
  have hE := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P L Ω l ι 2 r w hlw A hA a ha τ hτ hPT ψ hψs hsub
  let x : Fin 2 → Weil hA → ℂˣ := fun i t => ψ i (a t) * absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t)
  have hpol : ∀ t : Weil hA, (r (t : G L Ω)).val.charpoly.map ι.toRingHom = (X - C (x 0 t : ℂ)) * (X - C (x 1 t : ℂ)) := by
    intro t
    rw [hE t, psPol, Fin.prod_univ_two]
  have hUo : ∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1 := by
    intro i u hu
    obtain ⟨t, rfl⟩ := ha.surj u
    have hd : deg t = 0 := by
      have h0 := ha.ord_eq t
      rw [ord_eq_zero_iff.2 hu] at h0
      omega
    have hI : (t : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.1 hd
    have h1 := hpol t
    rw [hunr A hA _ hI] at h1
    have h2 : ((1 : GL (Fin 2) (Qbar l)).val.charpoly).map ι.toRingHom = (X - 1 : ℂ[X]) ^ 2 := by
      simp [Matrix.charpoly_one]
    rw [h2] at h1
    obtain ⟨h3, h4⟩ := GoodWeilCharpoly.one_of_sq h1
    have hv := isUnram_absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t) hu
    have hx : ∀ j, x j t = ψ j (a t) := fun j => by
      show ψ j (a t) * _ = _
      rw [hv, mul_one]
    have e0 : ψ 0 (a t) = 1 := Units.ext (by rw [← hx 0]; exact h3)
    have e1 : ψ 1 (a t) = 1 := Units.ext (by rw [← hx 1]; exact h4)
    fin_cases i
    · exact e0
    · exact e1
  let s' : Weil hA := ⟨s, mem_Weil_of_isFrob hA hF⟩
  let al : (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom (x 0 s')
  let be : (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom (x 1 s')
  have hal : ι (al : Qbar l) = (x 0 s' : ℂ) := by simp [al]
  have hbe : ι (be : Qbar l) = (x 1 s' : ℂ) := by simp [be]
  have hc : (r s).val.charpoly = (X - C (al : Qbar l)) * (X - C (be : Qbar l)) := by
    apply Polynomial.map_injective ι.toRingHom ι.injective
    have h1 := hpol s'
    rw [show ((s' : G L Ω)) = s from rfl] at h1
    rw [h1, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_C]
    simp [hal, hbe]
  have H : ∀ m : ℤ, |m| ≤ 2 → (ψ 0 / ψ 1) ^ 2 ≠ absPow (Kw w) (m : ℂ) := by
    intro m hm he
    apply hs
    refine ⟨m, hm, ?_⟩
    have h1 := congrArg (fun f : (Kw w)ˣ →* ℂˣ => ((f (a s') : ℂˣ) : ℂ)) he
    have h2 := (_root_.UpperTheory.V.Z.Sym.Ga.cyc_char_eq_abs_pow_and_norm_pow_deg_away_l P L Ω l ι w hlw A hA a ha s').1
    have hq : (x 0 s' : ℂ) / (x 1 s' : ℂ) = (ψ 0 (a s') : ℂ) / (ψ 1 (a s') : ℂ) := by
      simp only [x, Units.val_mul]
      exact mul_div_mul_right _ _ (Units.ne_zero _)
    simp only [MonoidHom.pow_apply, MonoidHom.div_apply, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val,
      GoodWeilCharpoly.absPow_int_val, ← h2, ← hq, ← hal, ← hbe] at h1
    have h3 : ((al : Qbar l) / be) ^ 2 = Ga.ep l s ^ m := by
      apply ι.injective
      simpa [map_zpow₀] using h1
    have h4 := (Ga.ufFacts (Qbar l) (r s)).1 al be hc
    have hne : ((al : Qbar l) / be) ≠ 0 := div_ne_zero al.ne_zero be.ne_zero
    have h5 : ((al : Qbar l) / be)⁻¹ ^ 2 = Ga.ep l s ^ (-m) := by rw [inv_pow, h3, zpow_neg]
    rw [h4]
    simp only [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    rw [← h3, ← h5]
    field_simp
    ring
  exact ⟨ψ, hψs, ⟨e⟩, hUo, ⟨fun y hy => by simp [MonoidHom.div_apply, hUo 0 y hy, hUo 1 y hy], H⟩⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
variable {l : ℕ} [Fact l.Prime]
section Pt
variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
variable {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)
variable (T : TWGrp G0)
end Pt
section Mod
variable {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) (x : B →ₐ[O] O)
variable {b} {G : Glob l L} {h : G.Hom G0} {q N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ)
end Mod
section Bar
variable (F : GFrame l) {n : ℕ} (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)]
  (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))
end Bar
section Ar
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev}
def LevelAtOrdinaryDeterminantRing {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r}
    {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D) : Prop :=
  ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
    (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
    V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
    (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
variable {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
def LevelIdealCondition (J : Ideal B.B) : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b ∧ (∀ k, b.wt.γ k ∈ V0.frame.Iv (b.wt.v k)) ∧
    ∀ (x : B.B →ₐ[c.O] c.O) (h : s.Wt n), (barPt B x).Arith h → CtrlH b x
end Ar
def HidaFamilyCondition : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (n : ℕ), 1 ≤ n →
    ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ), ∃ J : Ideal B.B, B.PointTheoremBaseObject ι J ∧ _root_.UpperTheory.V.Th.LevelIdealCondition B J
def HasHeckeOperatorDense : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ)
    (b : TWBase (pairOf B.u) J Empty D), _root_.UpperTheory.V.Th.LevelAtOrdinaryDeterminantRing b → ∀ T : TWGrp (globOf r V0), TWPl r T → OpAt b T
def OrdinaryMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B)
    (y : Pt (globOf r V0).frame c.O n) (x : B.B →ₐ[c.O] c.O) (h : s.Wt n) (q : ℕ) (sg : Fin q → V0.frame.G₀)
    (al : Fin q → Fin n → c.O), V0.S' = s.S → 1 ≤ n → _root_.UpperTheory.V.Th.LevelIdealCondition B J → J ≤ RingHom.ker x → (barPt B x).Arith h →
    B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → y.N4 V0.frame.D0 →
    (∀ j, sg j ∈ V0.frame.G' ∧ Function.Injective (al j) ∧
      (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range sg) →
    ∀ δ : B.B →ₗ[c.O] c.O, IsDer x δ → (∀ v i, ∀ g ∈ V0.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) →
      ∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = 0
end UpperTheory.V.Th
end
end
end

