import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk098

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360858708824610169, 360858709346010353⟩, ⟨(-2752584873776226790), (-2752581410034282798)⟩, true⟩

def state01 : KState := ⟨⟨360766128502049942, 360766129024575729⟩, ⟨(-1845221191675215305), (-1845217716896933991)⟩, true⟩

def words00 : List Nat := [360577883135019230, 360577904087740087, 360577935406565210, 360577966719036507, 360577992321837375, 360578007674173214, 360578015235927823, 360578022796151794, 360578033436581158, 360578052608624559]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360710519184165506, 360710519707804280⟩, ⟨(-1298807070268405838), (-1298803584565940614)⟩, true⟩

def words01 : List Nat := [360578082133414047, 360578111652209249, 360578135869457879, 360578160502061344, 360578179059871008, 360578197613930501, 360578226510369021, 360578245180172992, 360578258650190520, 360578272117480898]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360741763663218393, 360741764187977075⟩, ⟨(-1606491876023495096), (-1606488379318140422)⟩, true⟩

def words02 : List Nat := [360578281327213172, 360578295657729089, 360578306215835860, 360578316771815074, 360578318217853159, 360578318217971900, 360578319629502720, 360578323197478567, 360578337089246451, 360578353713018461]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360746087903184098, 360746088429070143⟩, ⟨(-1648984910229015278), (-1648981402435971224)⟩, true⟩

def words03 : List Nat := [360578364097459923, 360578374479802077, 360578395179784328, 360578424224643112, 360578446293108557, 360578468357104795, 360578485263038351, 360578491985863634, 360578509018118607, 360578526046950850]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360739294187849523, 360739294714855544⟩, ⟨(-1581939993670157238), (-1581936474851018566)⟩, true⟩

def words04 : List Nat := [360578545835076240, 360578570946788504, 360578588859183126, 360578606767951737, 360578617800559432, 360578634303675589, 360578656467852466, 360578678627551055, 360578692026930489, 360578708330239666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361052070411729400, 361052070939856763⟩, ⟨(-4664647129171140788), (-4664643599301179750)⟩, true⟩

def words05 : List Nat := [360578734917108813, 360578761498615608, 360578793988532937, 360578823878221923, 360578845047421778, 360578866212337430, 360578897647358452, 360578935368149076, 360578983353597469, 360579031329340469]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360823356972754854, 360823357502016374⟩, ⟨(-2409385994092904855), (-2409382453034572059)⟩, true⟩

def words06 : List Nat := [360579073023070890, 360579104571489795, 360579135573534584, 360579166569328063, 360579194792096425, 360579212876346528, 360579221753407200, 360579230628680627, 360579245804509477, 360579270534836294]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360612986392391400, 360612986922774431⟩, ⟨(-331372366149808403), (-331368814016446217)⟩, true⟩

def words07 : List Nat := [360579305504191194, 360579340466484889, 360579370340865137, 360579390090870786, 360579406299589494, 360579422505057197, 360579433966327273, 360579444173883670, 360579447569004996, 360579450963456908]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360773075888790066, 360773076420298308⟩, ⟨(-1913557469383150052), (-1913553906127098806)⟩, true⟩

def words08 : List Nat := [360579459686481967, 360579474356425328, 360579499245831944, 360579524130227406, 360579540480881128, 360579546734094107, 360579563203578727, 360579579669767006, 360579592708736170, 360579612270452277]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360773572439630494, 360773572972278653⟩, ⟨(-1918768716412033272), (-1918765141876730310)⟩, true⟩

def words09 : List Nat := [360579623516541184, 360579634760366840, 360579648769589436, 360579670756046835, 360579689987378112, 360579709214842535, 360579723195029714, 360579738732031823, 360579758311345011, 360579777886744189]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk098
