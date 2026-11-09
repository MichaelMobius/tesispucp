# Decimotercera etapa. Convergencia uniforme y tasas del Teorema 3.8

El Lema 3.3 y la Hipótesis 3.2 se encuentran en las páginas impresas 43–47. El Teorema 3.8 enuncia (3.27)–(3.28) en las páginas 66–67. En dimensión dos, (3.27) exige convergencia a cero de las normas supremo del residuo interior y del residuo de frontera. Los exponentes de (3.28) son `−α²/[2(2α+2)]` y `−α²/[2(2α+1)]`, ambos en función de `mr(n)`.

## Correspondencia de la prueba

| Paso | Declaración |
|---|---|
| Lema 3.3. Seleccionar la celda que contiene al centro a escala `η=r/(2√2)`. Su diámetro no supera `r/2`, de modo que la celda está contenida en la bola abierta intersectada con el soporte. | `masa_bola_inferior_de_particiones`, `masa_bola_inferior_potencia` |
| Para cualquier radio admisible, usar la cota Hölder y comparar la integral cuadrática en la bola con la integral global. | `abs_le_holder_add_de_integral` |
| Si el radio solicitado excede el umbral geométrico, aplicar la misma comparación en `min(r,R)`. Se admite energía cero. | `supResiduo_le_radio_truncado` |
| Con una envolvente `C m^(-β)`, usar eventualmente el radio `m^(-β/(2α+s))`. La cota uniforme es `(H+√(C/κ)) m^(-βα/(2α+s))`, donde `H` es la cota Hölder y `κ` la constante de masa local. | `tasa_supResiduo_de_integral` |
| Obtener el control Hölder de ambos residuos mediante minimalidad y la regularidad uniforme del comparador. | `holder_residuos_minimizador` |
| Usar (3.26), dividir la cota entre cada peso residual positivo y aplicar la transferencia con `β=α/2`, primero con `s=2` y después con `s=1`. | `convergencia_y_tasas_uniformes_ae` |

`supResiduo` representa el supremo puntual de valores absolutos en el dominio correspondiente. La cota vale uniformemente sobre cada dominio y no requiere que el supremo se alcance. Las constantes pueden depender de la realización por la constante de (3.26) y la cota del comparador.

## Hipótesis y composición con la PR #14

- `ParticionesMinimas` cuantifica sobre cada escala admisible, conforme a la Hipótesis 3.2. La PR #14 parametriza las particiones a la sucesión discreta usada para ocupación. Sin un control adicional de las razones entre escalas sucesivas, esa información discreta por sí sola no da la cota local a todos los radios.
- La transferencia recibe como `h26` la parte de cota eventual del resultado `tasa_poblacional_eventual_casi_segura`. Se usa la misma familia `problemaMuestral`, las mismas medidas y los mismos pesos. El crecimiento eventual `mr(n)≥n` implica el antecedente `Tendsto mr atTop atTop`.
- `hstats` contiene las propiedades variacionales sobre un evento de medida plena. La positividad e igualdad de los pesos se verifican con (3.23). La integrabilidad visible en esa interfaz se obtiene de continuidad, cotas Hölder, acotación y concentración mediante los lemas de `TasaPoblacional.lean`. La prueba usa la cota uniforme del comparador para deducir la de los minimizadores.
- La versión Lean abstrae los dominios como espacios pseudométricos con dimensiones de masa 2 y 1. No construye clases de redes, comparadores ni selecciones. La regularidad de estas clases corresponde a la Hipótesis 3.7.

## Mensurabilidad

`measurable_perdidaPoblacional_seleccion` usa la mensurabilidad conjunta de `(h,x)↦L[h](x)` y `(h,y)↦B[h](y)`, la mensurabilidad de los datos y la de la selección. Se compone la selección con cada operador y se aplica la mensurabilidad de la integral de Bochner respecto de una medida fija. Las muestras empíricas no intervienen en la pérdida poblacional. Para instanciar este lema con funciones definidas solo en los soportes, se pueden usar operadores sobre subtipos o extensiones medibles a los espacios ambiente.

Las selecciones mensurables y la continuidad espacial por candidato de la Hipótesis 3.7 no implican por sí solas mensurabilidad conjunta para un tipo abstracto de candidatos. La transferencia de (3.26) a las conclusiones uniformes está formulada mediante `∀ᵐ`. El lema de mensurabilidad permite además usar el resultado de probabilidad uno del evento concreto de tasa poblacional de la PR #14 cuando se verifican sus antecedentes.

## Verificación reproducible

El módulo se importa desde `TesisPINN.lean` y se verifica con `lake build`. Las directivas `#print axioms` del módulo registran las dependencias en la misma ejecución. Se mantienen Lean y Mathlib en `v4.35.0` y EllipticPDE en `c47acceaf985f59e1cf3257ffea077a73ea99dae`. El historial de compilación de cada revisión está en los controles de la [PR borrador #15](https://github.com/MichaelMobius/tesispucp/pull/15/checks).
