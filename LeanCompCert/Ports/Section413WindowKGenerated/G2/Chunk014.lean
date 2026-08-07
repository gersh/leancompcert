import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk014

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360517311008598450, 360517311017129812⟩, ⟨(-6965126602781780), (-6965118461170710)⟩, true⟩

def state01 : KState := ⟨⟨360092653931579902, 360092653940243106⟩, ⟨582115603417661883, 582115611744516451⟩, true⟩

def words00 : List Nat := [360512339483622368, 360512093005967971, 360511360191003381, 360510766620624130, 360510173895181194, 360509447111521144, 360508659446922017, 360507444127725368, 360506230533606550, 360505501891834962]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨358672209090942588, 358672209099737462⟩, ⟨2596032097417378266, 2596032105930569042⟩, true⟩

def words01 : List Nat := [360505209299393029, 360505024079282289, 360504839121335918, 360504378807434778, 360503995519454574, 360503482861696643, 360502970927516684, 360502567486419488, 360501689089807917, 360500400723632229]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360742573480908700, 360742573489836756⟩, ⟨(-359353554068221985), (-359353545365256203)⟩, true⟩

def words02 : List Nat := [360499114170776935, 360497684379766519, 360496526125956770, 360495842566292146, 360495159966008444, 360494071786468950, 360492900251788391, 360492201466560037, 360491503659333355, 360491452913061595]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360470055224248417, 360470055233311158⟩, ⟨31870676641605973, 31870685537865645⟩, true⟩

def words03 : List Nat := [360491452913074290, 360491355135630931, 360491628524194347, 360492257423973893, 360492480507883263, 360492703281309164, 360492703281321809, 360492684368461705, 360492203034224655, 360492187653823565]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360450063264829617, 360450063274027100⟩, ⟨59219704970591119, 59219714061555847⟩, true⟩

def words04 : List Nat := [360492184523651507, 360492262149906565, 360492262149919334, 360491979935462540, 360491698111611698, 360491139931462125, 360490986823828542, 360491140601996147, 360491140602009224, 360490904456138518]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361753879071391500, 361753879080724609⟩, ⟨(-1838686450997533260), (-1838686441709221678)⟩, true⟩

def words05 : List Nat := [360491306985581217, 360491737069139067, 360492624735427743, 360493059651190740, 360493059651203964, 360493059156550164, 360493232741030789, 360493641629218056, 360494504805566414, 360495366800293931]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360444901718497789, 360444901727969159⟩, ⟨74071196976190570, 74071206467055822⟩, true⟩

def words06 : List Nat := [360495992379082896, 360496577597320991, 360496833546231010, 360497089145726595, 360497219530669806, 360497219530684333, 360496905463937274, 360496333642595590, 360495762599769093, 360495290303797089]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359267412357388462, 359267412366997313⟩, ⟨1817006419165768717, 1817006428859441607⟩, true⟩

def words07 : List Nat := [360495668839494976, 360496081069360192, 360496261785315665, 360496452422517303, 360496453262343064, 360496454101035501, 360496454101047569, 360496420388973081, 360495949506170427, 360495119413523963]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361263215592057245, 361263215601804912⟩, ⟨(-1145828243028820287), (-1145828233128999353)⟩, true⟩

def words08 : List Nat := [360494290441863709, 360493903613822749, 360494202346925162, 360494571488099943, 360494571488113685, 360494494110659723, 360493982285918177, 360493909841484749, 360494203364790371, 360494719134246898]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361607021960278843, 361607021970167934⟩, ⟨(-1662492454543915623), (-1662492444432660101)⟩, true⟩

def words09 : List Nat := [360494867324357952, 360495015315957225, 360495599876495814, 360496420322906857, 360496906056342739, 360497391140838621, 360497648379209611, 360497954295400705, 360498693673862641, 360499432067148174]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk014
