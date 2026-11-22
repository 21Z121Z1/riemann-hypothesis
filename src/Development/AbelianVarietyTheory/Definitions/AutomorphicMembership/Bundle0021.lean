import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

def MatEq {A : Type} [CommRing A] {a b : ℕ} (x : GL (Fin a) A) (y : GL (Fin b) A) : Prop :=
  a = b ∧ ∀ (i j : Fin a) (i' j' : Fin b), (i : ℕ) = i' → (j : ℕ) = j' → x.1 i j = y.1 i' j'

section Gen

variable {X : Fields} {n : ℕ} [NeZero n] {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W] (σ : X.K →+* ℂ)
  (mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (rat : Γ → GL (Fin a) X.E → Prop) (ρ : Γ → W → W)

def StdSide {ι : Type} (lam : X.Tau → DomWeight n) (rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam))
    (SG : ι → Finset (Pl X.E)) (Fm : ι → Type) (val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam)
    (ad : ∀ t, Fm t → H → W) : Prop :=
  ∃ c : VV X.K lam →ₛₗ[σ] W,
    (∀ γ γE g, rat γ γE → MatEq γE g → ∀ v, c (rho g v) = ρ γ (c v)) ∧
    (∀ (hc : CMData X.F X.E) t (φ : Fm t) (h : H) (x : Formalism.L2.Col.UAd hc n), MatEq (mat h) (x : GL (Fin n) _) →
      ad t φ h = c (val t φ (decoPt hc n ∅ (SG t) (QuotientGroup.mk x)))) ∧
    (LinearIndependent ℂ fun i => c (bVV X.K lam i)) ∧
    ∃ hc : CMData X.F X.E, ∀ h : H, ∃ x : Formalism.L2.Col.UAd hc n, MatEq (mat h) (x : GL (Fin n) _)

theorem StdSide.value {ι : Type} {lam : X.Tau → DomWeight n} {rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)}
    {SG : ι → Finset (Pl X.E)} {Fm : ι → Type} {val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam} {ad : ∀ t, Fm t → H → W}
    (s : StdSide σ mat rat ρ lam rho SG Fm val ad) :
    ∃ c : VV X.K lam →ₛₗ[σ] W, (LinearIndependent ℂ fun i => c (bVV X.K lam i)) ∧
      ∀ h t, ∃ d : DecoSet X.E n ∅ (SG t), ∀ φ, ad t φ h = c (val t φ d) := by
  obtain ⟨c, -, hr, hli, hc, hx⟩ := s
  refine ⟨c, hli, fun h t => ?_⟩
  obtain ⟨x, hm⟩ := hx h
  exact ⟨_, fun φ => hr hc t φ h x hm⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def matIn {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (h : Bridge.Gf V) : GL (Fin V.rank) (Lev.EAf D) :=
  Formalism.UG.bc (swapAE D) (h : GL (Fin V.rank) _) * β

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)

set_option maxHeartbeats 2000000 in

def BrgStdR (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (cX : CoefA X.toD7.sp.X')
    (jR : ∀ t, (famR X I hX U Xg tr).A.fam.amb.FR t → Bridge.Gf X.toD7.sp.X' → cX.W) : Prop :=
  StdSide (X := X.B.fields) (n := X.B.R.N X.B.R.m - 1) (a := X.toD7.sp.X'.rank) (H := Bridge.Gf X.toD7.sp.X') (Γ := GQ X.toD7.sp.X')
    (W := cX.W) ((X.B.embLL)) ((matIn X.toD7.sp.X' L.βX)) ((Bridge.IsRatMat X.toD7.sp.X'))
    (fun γ v => cX.coef.ρ γ v) (ι := TupU I U) X.B.wts.sgTrue (rhoV X.B.fields.emb X.B.wts.sgTrue)
    (fun t => rowSG (X.B.primes px) I.sel t.1)
    (fun t => PLift (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).Ok ×
      (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).EqFun)
    (fun _ φ => φ.2.1)
    fun t φ => jR t ((by with_unfolding_all exact ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res φ.1.down φ.2 :)))

set_option maxHeartbeats 2000000 in

def BrgStdV (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (cV : CoefA (Vc X.toD7 i))
    (jL : ∀ t, (famR X I hX U Xg tr).A.fam.amb.FL i t → Bridge.Gf (Vc X.toD7 i) → cV.W) : Prop :=
  StdSide (X := X.B.fields) (n := X.B.R.nV) (a := (Vc X.toD7 i).rank) (H := Bridge.Gf (Vc X.toD7 i)) (Γ := GQ (Vc X.toD7 i))
    (W := cV.W) ((X.B.embLL)) ((matIn (Vc X.toD7 i) (L.βV i))) ((Bridge.IsRatMat (Vc X.toD7 i)))
    (fun γ v => cV.coef.ρ γ v) (ι := TupU I U) (X.B.wts.lamV ((i : ℕ) + 1)) (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)))
    (fun t => rowSG (X.B.primes px) I.sel t.1)
    (fun t => PLift (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok ×
      (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun)
    (fun _ φ => φ.2.1)
    fun t φ => jL t ((by with_unfolding_all exact ((mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res φ.1.down φ.2 :)))

def BrgStd {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 (famR X I hX U Xg tr).A Ks) : Prop :=
  BrgStdR X I hX U Xg tr R.toLevCh R.cX (fun t φ => R.B.jR t φ) ∧
    ∀ i, BrgStdV X I hX U Xg tr R.toLevCh i (R.cV i) fun t φ => R.B.jL i t φ

variable {X I hX} in

def Dat.Std {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : Prop :=
  BrgStd X I hX (usedOf I T Wt) z.Xg z.tr z.R.toRealDat

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Model

theorem mem_iff_trace {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (χ : G → K) :
    χ ∈ X ↔ IsAbsIrrChar χ ∧ ∑ g, (idemOf X).coeff g * χ g = χ 1 := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : IsAbsIrrChar χ → χ 1 ≠ 0 ∧ ∑ g, (idemOf X).coeff g * χ g = if χ ∈ X then χ 1 else 0 := fun h => by
    have h1 : χ 1 ≠ 0 := by
      obtain ⟨n, ρ, hρ, hχ⟩ := h
      intro e
      have h2 := hχ 1
      rw [e, map_zero, Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at h2
      exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    refine ⟨h1, ?_⟩
    simp only [coeff_idemOf, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_ite_eq' X χ fun _ => χ 1]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    have h3 := conv_char (hX ψ hψ) h 1
    simp only [mul_one] at h3
    apply mul_right_cancel₀ h1
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [h3]
    split_ifs with e
    · rw [e]; field_simp
    · simp
  refine ⟨fun h => ⟨hX χ h, by rw [(key (hX χ h)).2, if_pos h]⟩, fun ⟨h, e⟩ => ?_⟩
  by_contra hn
  rw [(key h).2, if_neg hn] at e
  exact (key h).1 e.symm

section Base

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

theorem mem_vGs_iff (h : I.Ok) (P : HeightOneSpectrum (𝓞 B.fields.E)) : P ∈ (B.primes px).vGs ↔ ∃ k, I.C.P.Div k P := by
  classical
  unfold Formalism.L2.Col.Primes.vGs
  rw [Finset.mem_union, h.pibar, h.pibar, Fin.exists_fin_two]

theorem ixOf_empty (t : TupU I ∅) : ixOf I ∅ t = I.mu0 := by
  rcases (mem_range_ixOf I (U := ∅) (a := ixOf I ∅ t)).1 ⟨t, rfl⟩ with e | e
  · exact e
  · exact e.elim

theorem exists_under_of_selHalf (h : SelHalf I) (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 B.host.K), ∀ a, ∀ P : HeightOneSpectrum (𝓞 B.host.E), P ∈ I.Q a →
      ((p : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal → P.under (𝓞 B.host.K) = 𝔭 := by
  by_cases e : ∃ a, ∃ P : HeightOneSpectrum (𝓞 B.host.E), P ∈ I.Q a ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal
  · obtain ⟨b, P', hb, hP'⟩ := e
    exact ⟨P'.under (𝓞 B.host.K), fun a P ha hP => HeightOneSpectrum.ext (h a b P ha P' hb ⟨p, hp, hP, hP'⟩)⟩
  · exact ⟨I.C.P.pb 0, fun a P ha hP => absurd ⟨a, P, ha, hP⟩ e⟩

theorem mem_level_of_local_depth (g : Gc B px) : g ∈ lev0 I ↔ ∀ w, g w ∈ unip (kP w.1) B.R.r :=
  ⟨fun h w => h w (Set.mem_univ _), fun h w _ => h w⟩

theorem baseLevel_eq_unipotent : lev0 I = (Formalism.L2.Col.rP0 (R := B.R) I.Ch).grp := by
  ext g
  rw [mem_level_of_local_depth]
  refine ⟨fun h w _ => ⟨fun i j hij => unip_lower (h w) ?_, fun i _ => unip_diag (h w) i⟩, fun h w =>
    ⟨fun i j hij => (h w (Set.mem_univ _)).1 ?_, fun i => (h w (Set.mem_univ _)).2 i i.2⟩⟩
  · exact (Formalism.L2.Col.fine_lt_right i.2).1 hij
  · exact (Formalism.L2.Col.fine_lt_right i.2).2 hij

theorem isGenericPsi_psiC (h : I.Ok) : IsGenericPsi (B.primes px).vGs (psiC I) := fun P hP => by
  rw [psiC_of_mem I hP]
  exact h.ch_ok.psi_zero_nontrivial_character _

theorem embLL_xiValOf_of_ok (h : I.Ok) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E)) :
    B.embLL (xiValOf I (I.tup a) P : B.LL) = (((I.xi a).val P : ℂˣ) : ℂ) :=
  embLL_xiValOf I a P ⟨_, (h.xi_reads a _).symm⟩

theorem valsIn_iff (h : I.Ok) : ValsIn I ↔ ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (kP P)) :=
  ⟨fun H => H.2, fun H => ⟨fun a _ _ => ⟨_, (h.xi_reads a _).symm⟩, H⟩⟩

end Base

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)

theorem exists_levOf_of (h : I.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (hC : L.C = Top.Fr.at X I.C) (hx : L.xiH = fun t => I.xi (ixOf I U t)) (hQ : L.Q = fun t => I.Q (ixOf I U t))
    (hL : L.Is (mu0F (X := X.B.fields) (tuOf I U))) : ∃ L', LevOf X I U L' := by
  have hd : DiagSpaces X.toD7.sp := h.spaces
  obtain ⟨hst, hstX⟩ := GlobalTheory.Mem.HostFrames.stdLat_diag hd
  refine ⟨{ L with βX := 1, βV := fun _ => 1, ΛX := Formalism.IndefR.Seed.FrmP.coordL _, ΛV := fun _ => Formalism.IndefR.Seed.FrmP.coordL _ },
    ⟨⟨hL.mu0, hL.eta, hL.xi, hL.xi_inj, hL.xi_base, hL.xi_fin, hL.xi_triv, hL.xi_tame, hL.Pg, hL.Q_pl, hL.Q_off, hL.Q_de,
      hL.Q_ram, hL.chi, hL.xiR, hL.βY, Formalism.IndefR.Seed.FrmP.isSDFrame_std _ hstX 1,
      fun i => Formalism.IndefR.Seed.FrmP.isSDFrame_std _ (hst _).2.1 1, hL.βW⟩, hC, fun t => congrFun hx t, ?_,
      fun t => congrFun hQ t, fun _ => rfl, rfl⟩⟩
  refine Finset.ext fun P => (hL.Pg P).trans ?_
  rw [hC]
  exact (mem_vGs_iff I h P).symm

theorem exists_levOf_empty (h : I.Ok) : ∃ L, LevOf X I ∅ L := by
  have hx : ∀ t : TupU I ∅, I.xi (ixOf I ∅ t) = 1 := fun t => by rw [ixOf_empty, h.trueColumnChoices_heckeChar_reference_eq_one]
  have hQ : ∀ t : TupU I ∅, I.Q (ixOf I ∅ t) = ∅ := fun t => by rw [ixOf_empty, I.twistPrimes_reference_tuple_eq_empty]
  have hn : ∀ (t : TupU I ∅) (P : Pl X.toD7.host.E), P ∉ I.Q (ixOf I ∅ t) := fun t P => by
    rw [hQ]; exact Finset.notMem_empty _
  obtain ⟨L, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I ∅)
    (mu0F (X := X.B.fields) (tuOf I ∅)) (fun t => I.xi (ixOf I ∅ t)) (fun t => I.Q (ixOf I ∅ t))
    (h.xi_inj.comp (ixOf_injective I ∅)) (hx _)
    (fun t => ⟨1, one_pos, by rw [hx]; exact one_pow 1⟩)
    (fun t => by rw [hx]; exact (Formalism.L2.Host.isPsi_one (H := X.toD7.host) 2).triv)
    (fun t => by rw [hx]; exact fun _ _ _ _ => rfl)
    (fun t P hP => absurd hP (hn t P)) (fun t P hP => absurd hP (hn t P))
    (fun _ _ => ⟨I.C.P.pb 0, fun t P hP => absurd hP (hn t P)⟩)
    (fun t P => by
      rw [hx]
      exact iff_of_false (fun h => h fun _ _ => rfl) (by
        rintro (e | ⟨P', e, -⟩)
        exacts [hn t _ e, hn t _ e]))
  exact exists_levOf_of X I h ∅ L h1 h2 h3 h4

theorem grpAt_iff (h : I.Ok) : GrpAt X I ↔ ∀ k v, I.C.P.Div k (X.toD7.naut.plGw k v) := by
  classical
  refine ⟨fun ⟨⟨plg, hp⟩, _, _⟩ k v => (hp ⟨k, v⟩).1 ▸ (hp ⟨k, v⟩).2, fun H => ?_⟩
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  refine ⟨?_, hi, hc⟩
  have hPr := (base_fields_primes_ok X.B px).2.1
  let φ : (Σ k : Fin 2, X.toD7.nd.PlG k) → (X.B.primes px).vGs :=
    fun kv => ⟨X.toD7.naut.plGw kv.1 kv.2, (mem_vGs_iff I h _).2 ⟨kv.1, H _ _⟩⟩
  have hinj : Function.Injective φ := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ e
    have e' : X.toD7.naut.plGw k v = X.toD7.naut.plGw k' v' := congrArg Subtype.val e
    have hk : k = k' := by
      have a := hPr.vG_norm k _ ((h.pibar k _).2 (H k v))
      have b := hPr.vG_norm k' _ ((h.pibar k' _).2 (H k' v'))
      have c : (X.B.primes px).g k = (X.B.primes px).g k' := a.symm.trans ((congrArg (fun P : HeightOneSpectrum (𝓞 X.B.fields.E) => Ideal.absNorm P.asIdeal) e').trans b)
      have := hPr.g_ne
      fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd c this | exact absurd c.symm this
    subst hk
    rw [X.toD7.naut.plGw_inj k e']
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    obtain ⟨k, hk⟩ := (mem_vGs_iff I h P).1 hP
    let ψ : X.toD7.nd.PlG k → (X.B.primes px).vG k := fun v => ⟨X.toD7.naut.plGw k v, (h.pibar k _).2 (H k v)⟩
    have hψ : Function.Bijective ψ := by
      refine (Fintype.bijective_iff_injective_and_card ψ).2 ⟨fun v v' e => X.toD7.naut.plGw_inj k (congrArg Subtype.val e), ?_⟩
      rw [X.toD7.nd.card_PlG k, Fintype.card_coe, hPr.vG_card k]
      exact (X.toD7.what₂.card_Tau).symm
    obtain ⟨v, hv⟩ := hψ.2 ⟨P, (h.pibar k P).2 hk⟩
    exact ⟨⟨k, v⟩, Subtype.ext (by have := congrArg Subtype.val hv; exact this)⟩
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, fun kv => ⟨rfl, H _ _⟩⟩

theorem grpAt_of_grpTrue (h : I.Ok) (hN : Top.GrpTrue X.N I.C) : GrpAt X I := (grpAt_iff X I h).2 hN.pl

theorem goodSet_of_idem (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) (hX : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (he : ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g)) : GoodSet X (px := px) eR Xg := by
  refine (goodSet_iff X eR Xg).2 ⟨fun χ => ?_, he⟩
  simp only [← he, ← map_mul, ← map_sum, X.B.embLL.injective.eq_iff]
  exact mem_iff_trace Xg hX χ

theorem GoodSet.nonempty {eR : Gc X.B px ≃* G0g X.toD7.nd} {Xg : Finset (Gc X.B px → X.B.LL)}
    (h : GoodSet X (px := px) eR Xg) (h0 : X.toD7.ntypes.e0 ≠ 0) : Xg.Nonempty := by
  by_contra e
  rw [Finset.not_nonempty_iff_eq_empty] at e
  apply h0
  apply MonoidAlgebra.ext
  ext t
  obtain ⟨g, rfl⟩ := eR.surjective t
  rw [← h.2 g, e]
  simp [idemOf]

theorem isIdG_iff (eG : Gc X.B px ≃* Gc X.B px) :
    IsPlacewiseIdentity X (px := px) (Pg := (X.B.primes px).vGs) eG ↔ eG = MulEquiv.refl _ :=
  ⟨fun h => MulEquiv.ext fun g => funext fun P => h g P.1 P.2 P.2, fun h => h ▸ isIdG_refl X⟩

end Record

end GlobalTheory.Mem.R3.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}

def levCh (L : Formalism.IndefR.Links.LevCh D T) (f : T' → T) : Formalism.IndefR.Links.LevCh D T' where
  C := L.C
  xiH t := L.xiH (f t)
  mu0 := L.mu0
  eta := L.eta
  xi t := L.xi (f t)
  Pg := L.Pg
  Q t := L.Q (f t)
  chi := L.chi
  xiR t := L.xiR (f t)
  ΛY := L.ΛY
  ΛX := L.ΛX
  ΛV := L.ΛV
  ΛW := L.ΛW
  βY := L.βY
  βX := L.βX
  βV := L.βV
  βW := L.βW

theorem levCh_is {L : Formalism.IndefR.Links.LevCh D T} {f : T' → T} (hf : Function.Injective f) {μ : T'} (h : L.Is (f μ)) :
    (levCh L f).Is μ where
  mu0 := h.mu0
  eta := h.eta
  xi t := h.xi (f t)
  xi_inj := h.xi_inj.comp hf
  xi_base := h.xi_base
  xi_fin t := h.xi_fin (f t)
  xi_triv t := h.xi_triv (f t)
  xi_tame t := h.xi_tame (f t)
  Pg := h.Pg
  Q_pl t := h.Q_pl (f t)
  Q_off t := h.Q_off (f t)
  Q_de p hp := (h.Q_de p hp).imp fun _ h' t => h' (f t)
  Q_ram t := h.Q_ram (f t)
  chi := h.chi
  xiR t := h.xiR (f t)
  βY := h.βY
  βX := h.βX
  βV := h.βV
  βW := h.βW

section Two

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

set_option maxHeartbeats 2000000 in

def dat2 (R : RealDat D (A.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat D (A.comap f μ) Ks where
  toLevCh := levCh R.toLevCh f
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := ⟨fun t => R.B.R (f t), fun i t => R.B.L i (f t), R.B.rankR, R.B.rankL⟩
  prX := R.prX
  HX t := R.HX (f t)
  HV i t := R.HV i (f t)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX t := R.jX (f t)
  jV i t := R.jV i (f t)
  νY t := R.νY (f t)
  fdY t := R.fdY (f t)
  ν0 := R.ν0
  fd0 := R.fd0
  νX t := R.νX (f t)
  fdX t := R.fdX (f t)
  νV i t := R.νV i (f t)
  fdV i t := R.fdV i (f t)
  νW := R.νW
  fdW := R.fdW
  ωY t := R.ωY (f t)
  ωX t := R.ωX (f t)
  ωP i t := R.ωP i (f t)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY t := R.vY (f t)
  vX t := R.vX (f t)
  vP i t := R.vP i (f t)
  ItY := R.ItY
  ItX := R.ItX
  ioY t := R.ioY (f t)
  ioX t := R.ioX (f t)
  Th t := R.Th (f t)
  BV := R.BV
  ioP := R.ioP
  thF i t := R.thF i (f t)
  thG i t := R.thG i (f t)
  nW := R.nW
  FW := R.FW
  mu := mu
  twPl := tw
  kap := R.kap
  lam i t := R.lam i (f t)
  err0 := R.err0

def bare2 (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) :
    Face D A where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat D (A.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem isGrp (h : R.IsGrp (bare2 _ P0 ψ0 P1 ψ1)) : (dat2 f μ R mu tw).IsGrp (bare2 _ P0 ψ0 P1 ψ1) :=
  ⟨fun t => h.red_R (f t), fun i t => h.red_L i (f t), h.levels, h.record, h.chiW⟩

set_option maxHeartbeats 2000000 in

theorem isFam (h : R.IsFam) : (dat2 f μ R mu tw).IsFam := by
  obtain ⟨g, c, l, ht⟩ := h.tie
  exact ⟨⟨g, c, l, ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq, ht.mapR, ht.mapL,
    fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, h.Sb, fun t => h.roots (f t), h.pl_onto, fun t => h.degR (f t),
    fun i t => h.degL i (f t), fun i t => h.muVal i (f t), h.etaVal⟩

set_option maxHeartbeats 2000000 in

theorem isModels (h : R.IsModels) : (dat2 f μ R mu tw).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, fun t => h.HX (f t), fun i t => h.HV i (f t), h.HE, h.HW, h.gE, h.gW, fun t => h.jX (f t),
    fun i t => h.jV i (f t), fun t => h.νY (f t), fun t => h.νY' (f t), h.ν0, fun t => h.νX (f t), fun i t => h.νV i (f t),
    h.νW, h.BV, h.order⟩

set_option maxHeartbeats 2000000 in

theorem exAt (e : R.ExAt) : (dat2 f μ R mu tw).ExAt :=
  ⟨fun k hk => (e.ItY k hk).imp fun _ h t => h (f t), e.ItX.imp fun _ h t => h (f t), fun t => e.ioY (f t), fun t => e.ioX (f t),
    fun t => e.Th (f t), fun i => (e.ioP i).imp fun _ h t => h (f t), fun i t => e.thF i (f t), fun i t => e.thG i (f t)⟩

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (h : p x) : OrZero p x :=
  ⟨fun _ => h, fun hn => absurd ⟨x, h⟩ hn⟩

set_option maxHeartbeats 2000000 in

theorem isChainW (h : R.IsChainW) (e : R.ExAt) : (dat2 f μ R mu tw).IsChainW :=
  ⟨fun t => h.ωY (f t), fun t => h.ωX (f t), fun t => h.vY (f t), fun t => h.vX (f t), fun t => h.ptY (f t), fun t => h.ptX (f t),
    fun k hk => orZero_of fun t => (h.ItY k hk).1 (e.ItY k hk) (f t), orZero_of fun t => h.ItX.1 e.ItX (f t),
    fun t => h.ioY (f t), fun t => h.ioX (f t), fun t => h.Th (f t)⟩

set_option maxHeartbeats 2000000 in

theorem isThPW (h : R.IsThPW) (e : R.ExAt) : (dat2 f μ R mu tw).IsThPW :=
  ⟨fun i t => h.ωP i (f t), fun i t => h.vP i (f t), fun i t => h.pt_theta i (f t),
    fun i => orZero_of fun t => (h.ioP i).1 (e.ioP i) (f t), fun i t => h.thF i (f t), fun i t => h.thG i (f t)⟩

theorem baseW (hf : Function.Injective f) (h : R.BaseW (bare2 _ P0 ψ0 P1 ψ1)) (e : R.ExAt) :
    (dat2 f μ R mu tw).BaseW (bare2 _ P0 ψ0 P1 ψ1) :=
  ⟨levCh_is hf h.lev, isGrp mu tw h.grp, isFam mu tw h.fam, isModels mu tw h.models, isChainW mu tw h.chain e, isThPW mu tw h.thP e⟩

end Two

end GlobalTheory.Mem.R3.Res

end
end

