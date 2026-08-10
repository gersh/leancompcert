import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk280A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk280B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk280A

def state06 : KState := ⟨⟨360549932415109567, 360549937123592055⟩, ⟨909267256760120915, 909356617740046853⟩, true⟩

def words05 : List Nat := [360582345060891557, 360582345996814830, 360582346295721877, 360582346387118289, 360582346387427956, 360582345937049259, 360582346302934029, 360582346303303724, 360582345855442420, 360582344700845799]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360545835150105057, 360545839862082558⟩, ⟨1024093284436671310, 1024182743504288966⟩, true⟩

def words06 : List Nat := [360582343546249459, 360582342577871072, 360582342249770478, 360582341464126406, 360582340678509489, 360582338811450514, 360582335680517047, 360582332231503190, 360582328782627060, 360582326600362013]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360531436335741586, 360531441051243825⟩, ⟨1428370075912690052, 1428459633937155368⟩, true⟩

def words07 : List Nat := [360582325300892800, 360582323359992031, 360582321419156203, 360582320325932469, 360582319870526268, 360582319091387795, 360582318312270270, 360582316537019278, 360582313932113076, 360582312120828482]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360552480343497500, 360552485062483552⟩, ⟨837295734146838599, 837385390014024791⟩, true⟩

def words08 : List Nat := [360582310309544560, 360582309763567877, 360582308693371205, 360582306458598569, 360582304223917585, 360582301324822091, 360582299170710637, 360582298281494881, 360582297392305141, 360582295863124849]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360626878611724777, 360626883334209667⟩, ⟨(-1253211916830531367), (-1253122162663310485)⟩, true⟩

def words09 : List Nat := [360582294802207015, 360582293707105312, 360582292611974835, 360582291884296108, 360582290987011436, 360582289012713225, 360582287038484861, 360582286651699282, 360582288239069408, 360582289826410539]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk280B
