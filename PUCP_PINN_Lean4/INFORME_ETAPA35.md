# Etapa 35 · peso raíz, C3.12 y auditoría del capítulo III

Base [PR #36](https://github.com/MichaelMobius/tesispucp/pull/36), commit `1b3fe97bbbba79ebb599a6e96280c92e7b365179`. La numeración corresponde al PDF normativo identificado en el [inventario](INVENTARIO_FORMAL_CAPITULO_III.md).

## Peso raíz de (3.94)

`perdida_minimizadores326_raiz` trabaja con la clase polinómica de la red cuadrática de L3.24 en $U=(-1,1)^2$, los mismos prefijos de `Muestreo38` y la ley uniforme normalizada. Para todo $m\ge 1$, el funcional tiene peso $a_m=2\sqrt 2\,m^{-3/4}/(3\pi)$, por `pesoRaizInterior_medio`. El nuevo enunciado del selector boreliano expone el desempate por norma euclídea mínima de los coeficientes. La declaración anterior permanece disponible con su firma original. El selector se construye para el peso raíz. El índice artificial $m=0$ recibe peso positivo auxiliar y queda fuera de las conclusiones de minimización y frontera.

`cotas_minimizador326` usa el comparador exacto de Hermite y da las tres cotas de (3.91) con una sola constante $R$: $J_m\le a_mR$, $E_m\le a_mR$ y $[\Delta h_m]^2_{1/2;U}\le R$ para toda muestra interior. La concentración de la ley da simultáneamente la pertenencia de los puntos de todos los prefijos al cuadrado. Por `ocupacion311`, las coberturas valen eventualmente casi seguramente. El umbral geométrico es $m\ge324$.

La estimación de P3.11 produce

\[
E(h_m)\le C_m a_m R + 3r_m[f]^2_{1/2;U}
         = 9\sqrt 2\,(R+[f]^2_{1/2;U})\,m^{-1/4}.
\]

Aquí $C_m=(27\pi/2)\sqrt m$ y $r_m=3\sqrt 2\,m^{-1/4}$. La identidad $C_ma_m=3r_m$ usa $2\alpha=1$. El término de la fuente tiene el mismo exponente porque se evalúa con ese mismo radio y el dato manufacturado tiene seminorma Hölder finita.

`convergencia_neuronal_manufacturada_raiz` conserva el selector obtenido y prueba mensurabilidad de sus pesos de salida, Dirichlet homogéneo y mínimo global de `funcional311` para todo $m\ge1$. En el evento casi seguro de la tasa poblacional, reutiliza la cota de C3.23 y el factor dos de la normalización:

\[
\|h_m-u^*\|_{H^1(U)}+\|h_m-u^*\|_{L^\infty(U)}
\le 2\left(\frac{\sqrt2}{\pi}\sqrt{1+\frac2{\pi^2}}+\frac{26404}{100000}\right)\sqrt{E(h_m)}.
\]

La raíz de $m^{-1/4}$ es $m^{-1/8}$. La cota conjunta da esa tasa y convergencia de ambas normas. Para la red y la solución clásicas, el supremo del error en la clausura coincide con su norma esencial. El error Lean usa $h_m-u^*$, de modo que su laplaciano es $\Delta h_m-f$ con $f=-2\pi^2u^*$. La versión con peso logarítmico sigue aplicándose a sus propios minimizadores.

## Corolario 3.12

Las pp. 80–81 exigen un espacio de entrada $C^{2,\alpha}$, operadores lineales continuos hacia los espacios $C^{0,\alpha}$ interior y de frontera, una solución exacta y comparadores admisibles con (3.56). El corolario deriva (3.36)–(3.37) y exige además $\delta_m=O(a_m)$ para aplicar el resultado de minimización aproximada. El decaimiento $a_m\to0$ se usa para la cota uniforme del regularizador.

`RealizacionHolder312` codifica el espacio de llegada mediante un espacio normado real y una evaluación lineal. Exige que la norma domine cada valor absoluto y proporcione una constante Hölder en el soporte. La seminorma que se emplea en el funcional es el ínfimo exacto de constantes Hölder. Estas condiciones se satisfacen con las normas Hölder usuales, sea que se tome la suma o el máximo de sus dos componentes. El espacio normado de entrada y la cota (3.56) representan la aproximación fuerte. La demostración funciona con espacios de entrada y salida abstractos que satisfacen esa interfaz. Por tanto, la construcción de un modelo concreto de $C^{2,\alpha}(\overline U)$ y de sus operadores queda a cargo de cada instanciación que lo necesite.

`RealizacionHolder312.cota_residuo` identifica cada residuo con la evaluación del operador aplicado a $v_m-u^*$ sobre su dominio. Controla su supremo y su constante Hölder por la norma del operador multiplicada por $\|v_m-u^*\|$. `corolario312` promedia los cuadrados de las cotas puntuales con exactamente $\lambda_r/m_r$ y $\lambda_b/m_b$. Devuelve una cota $K a_m$ válida para todos los prefijos y una cota $R$ para la suma de seminormas al cuadrado. $K$ puede tomarse como $\lambda_r(\|\mathcal L\| A)^2+\lambda_b(\|\mathcal B\| A)^2$.

`corolario312_premisas310` usa la misma `Operadores38.base` y el mismo `problemaMuestral` de P3.10. A partir de la concentración de las leyes deduce soporte de todas las muestras a la vez. Entrega las cotas Hölder de datos y operadores, las premisas de regularidad y pérdida del comparador con $\varepsilon_m=K a_m$, y (3.42) con constante $K+K_\delta$. El comparador de (3.56) puede elegirse determinista y su selección constante respecto de la muestra es medible. La selección del mínimo aproximado, su mensurabilidad, las hipótesis de crecimiento y la cota de su brecha siguen siendo las condiciones de P3.10. El puente de esa proposición usa dimensiones de masa 2 y 1, mientras que el criterio determinista no usa dimensión.

`corolario312_taylor` comprueba las condiciones deterministas para el Poisson manufacturado usando las cotas de P3.27. Conserva la pertenencia a la clase, Dirichlet exacto, el seminorma real del laplaciano y ambas tolerancias. Es una instancia del criterio de comparación para una muestra interior y es válida desde $m=3$. La aproximación fuerte por sí sola no da igualdad exacta de trazas.

## Alcance del capítulo auditado

El [inventario](INVENTARIO_FORMAL_CAPITULO_III.md) coteja los 27 rótulos, sus páginas impresas, declaraciones, hipótesis, cuantificación, conclusiones y dependencias axiomáticas. Incluye las hipótesis H3.2, H3.7 y H3.16 como interfaces o premisas. La [matriz de ecuaciones](INVENTARIO_FORMAL_CAPITULO_III.md#ecuaciones-numeradas) separa definiciones, pasos derivados, condiciones de aplicación y fórmulas que aún carecen de una declaración con el alcance literal.

- **L3.1, H3.2 y H3.7.** L3.1 usa derivadas de Fréchet y salida escalar. La formulación multiíndice literal para la arquitectura general aún requiere el puente entre representaciones. H3.2 se consume por propiedades de masa y leyes de cada familia. La ley Hausdorff, la densidad de frontera y la independencia mutua de las familias no se reconstruyen del dato de masa. H3.7 presupone clases admisibles y selecciones para el modelo de dos muestras. La construcción neuronal verificada cubre el problema manufacturado de una muestra interior.
- **L3.3–T3.8.** Las afirmaciones combinadas de cobertura, generalización y tasa todavía usan los exponentes 2 y 1. En L3.6, el recuento y la cota probabilística ya admiten celdas que se solapan en conjuntos nulos. La versión geométrica agrupada usa celdas literalmente disjuntas y el factor $\sqrt2$. T3.8 conserva tanto la afirmación de muestra finita en evento medible como las tres conclusiones en un evento casi seguro común para la instancia 2D. La mensurabilidad de la pérdida se obtiene por el lema de mensurabilidad conjunta con las hipótesis sobre los operadores y la selección. La rama $d=1$ es una obligación distinta.
- **L3.9.** Las cotas a radio truncado y las transferencias de tasas están probadas. Falta la declaración global (3.34) con una constante uniforme para toda función del conjunto normado por el mismo control Hölder. Las pruebas integradas de las tasas 2D reutilizan la transferencia ya verificada.
- **H3.16, T3.18 y T3.20.** L3.17 verifica la estabilidad por barrera con coeficientes y solución dados. La existencia clásica bajo esfera exterior sigue siendo una dependencia matemática fuera de T3.18 Lean y T3.18 integrado usa la rama probabilística 2D. En T3.20 las instancias de Poisson prueban (3.72)–(3.74) para las clases suaves del cuadrado, con cota inferior de densidad y las premisas muestrales explícitas. La traza y el análisis espectral del cuadrado se reutilizan en C3.23. Permanece la extensión integrada de T3.20 al dominio Lipschitz general y la ruta alternativa (3.75) con ese alcance.

Para la aplicación manufacturada, quedan verificadas la existencia de comparadores y mínimos, la selección boreliana de los pesos, ambos regímenes y las tasas de aproximación de Taylor. El capítulo general todavía requiere las extensiones dimensionales de los resultados de cobertura y generalización, la cota global L3.9 y los puentes de existencia clásica y dominios generales. La formalización de reglas de cadena por multiíndices daría correspondencia literal con las fórmulas de L3.1. Las afirmaciones normativas de hipótesis permanecen como premisas cuando el texto las supone.

## Reproducción

Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. El PDF conserva SHA-256 `c6c612f7141c8c6ab5730fc0853b6d16222b97e5615e306f2e32191a49b686e0`.

`lake build` completó 3933 trabajos. Las declaraciones nuevas incluyen `#check` y `#print axioms`. El control adicional de las declaraciones principales de los 27 rótulos reportó `propext`, `Classical.choice` y `Quot.sound`.
