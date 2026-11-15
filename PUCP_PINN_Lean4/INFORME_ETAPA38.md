# Etapa 38 · T3.4 y T3.8 en dimensión uno y P3.10 dimensional

Base [PR #39](https://github.com/MichaelMobius/tesispucp/pull/39), commit `4a9f8a6f15003f0aa425bbe350c0a64de540f5e9`. Se compararon las pp. impresas 48–51, 66–77 y 80–81 del PDF normativo con la excepción unidimensional de la Assumption 3.1 y los Teoremas 3.1 y 3.2 del artículo. [Shin, Darbon y Karniadakis](https://arxiv.org/pdf/2004.01806)

## T3.4 unidimensional y (3.12)

`OperadoresPINN1D` fija los dos operadores, sus datos y la seminorma Hölder interior. Para $a<b$, `teorema34_unidimensional` identifica la frontera topológica de $(a,b)$ con $\{a,b\}$. La contribución determinista es

\[
E_{\partial U}(h)=\tfrac{\lambda_b}{2}
  \big(|B[h](a)-g(a)|^2+|B[h](b)-g(b)|^2\big).
\]

Esta misma expresión se suma al promedio interior en la pérdida empírica y a la integral interior en la poblacional. El funcional agrega únicamente $\widehat\lambda_{Rr,m}[L[h]]_{\alpha;U}^2$. No hay muestras de frontera. La concentración y Hölder en el intervalo acotado implican integrabilidad cuadrática.

Se usa `DatosMasaDimensional` con diámetro $D=1$ y exponente de masa $s=1$, tal como exige $\sqrt d=1$. La escala (3.5) da $\varepsilon_r=c_r^{-1}m_r^{-1/2}$. La pertenencia de todos los puntos al intervalo se intersecta con el evento medible de ocupación de las celdas. El complemento del evento de pertenencia es nulo. En consecuencia, la probabilidad es al menos $1-\sqrt{m_r}(1-1/\sqrt{m_r})^{m_r}$, y un solo evento permite sustituir cualquier candidato admisible, incluso uno elegido tras observar la muestra.

`factor34Unidimensional_eq` y `factor34Unidimensional_isBigO` verifican

\[
C^{(1)}_{m_r}=\max(1,3C_r m_r\varepsilon_r)
=\max(1,3(C_r/c_r)\sqrt{m_r})=O(\sqrt{m_r}).
\]

El máximo con 1 absorbe exactamente la contribución determinista de los extremos y es el factor del PDF. El artículo escribe $3(C_r/c_r)\sqrt{m_r}$ para su régimen de tamaños, donde la segunda expresión domina 1 eventualmente. El producto $C^{(1)}_{m_r}\widehat\lambda_{Rr,m_r}$ cancela el denominador y vale $3\lambda_r c_r^{-2\alpha}m_r^{-\alpha}$. La cota de Voronoi para el interior y la cancelación del promedio dan (3.12), incluido su término de datos $3\lambda_r c_r^{-2\alpha}[f]_{\alpha;U}^2m_r^{-\alpha}$.

## T3.8 unidimensional

`teorema38_unidimensional_evento` aplica la cota de muestra finita sobre el evento de (3.12). El mínimo global se compara con un interpolador cuya pérdida empírica total es cero, incluidos los dos extremos. La regularidad cuadrática queda acotada por $R$, y el objetivo queda a lo sumo en $\widehat\lambda_{Rr,m_r}R$. Esto da la cota poblacional del PDF con constante $3\lambda_r c_r^{-2\alpha}(R+[f]_{\alpha;U}^2)$.

`teorema38_unidimensional` conserva las selecciones mensurables, la existencia hipotética de los mínimos y comparadores, y un control uniforme $R$ que puede depender de la realización. Para tamaños $m_r(n)\ge n$ eventualmente, las particiones admisibles y Borel–Cantelli dan cobertura eventual de los mismos prefijos. La concentración y las premisas variacionales se combinan con la cobertura en un único evento casi seguro. La declaración `evento_prob_uno_de_ae` permite tomar un evento medible de probabilidad uno dentro del conjunto de realizaciones que cumplen todas las conclusiones.

La pérdida poblacional es $O(m_r^{-\alpha})$. El término interior da energía $L^2$ cuadrática del mismo orden y la regularidad del minimizador da una constante Hölder $\sqrt R+S_f$ para el residuo. L3.3 con exponente 1 aporta masa local $(c_r/2)r$, válida hasta radio $2\varepsilon_0$. La aplicación de L3.9 demuestra convergencia uniforme interior y tasa $O(m_r^{-\alpha^2/(2\alpha+1)})$.

El supremo interior se toma en $(a,b)$, como en la demostración unidimensional del PDF. Para la frontera, `max_residuo_extremos_le_raiz` usa la positividad de los dos cuadrados y obtiene

\[
\max(|B[h](a)-g(a)|,|B[h](b)-g(b)|)
\le \sqrt{2/\lambda_b}\,\sqrt{\operatorname{Loss}(h)} .
\]

Cada residuo y su máximo tienen tasa $O(m_r^{-\alpha/2})$ y tienden a cero sobre el mismo evento. El PDF explicita la convergencia de los residuos en esta rama. Las dos tasas uniformes son consecuencias cuantitativas de sus cotas. Para el máximo de frontera no se usa interpolación Hölder en dimensión cero.

## P3.10 y C3.12

`cotas310_dimensional_bajo_cobertura` obtiene (3.39)–(3.41) para comparadores aproximados. Usa la suboptimalidad respecto de cualquier admisible, equivalente a la cota respecto del ínfimo por `ProblemaPINN.minimizadorAproximado_iff_le_infimo`. Mantiene la penalización común $a_m$ de (3.23) y la pérdida del comparador $\le\varepsilon_m$. La cota de regularidad es $R+(\varepsilon_m+\delta_m)/a_m$. La desigualdad determinista también puede usarse con los radios positivos y el peso común de P3.14. Los mínimos del régimen raíz y del logarítmico corresponden a sus propios funcionales.

`proposicion310_dimensional` verifica (3.42)–(3.43) para exponentes $s_r,s_b>0$. Con $m_r\le K_{\rm size}m_b^{s_r/s_b}$ eventualmente y $\varepsilon_m+\delta_m\le Ka_m$, la regularidad total es a lo sumo $R+K$ y las dos seminormas son a lo sumo $\sqrt{R+K}$. El mismo evento da pérdida $O(m_r^{-\alpha/s_r})$ y ambas tasas uniformes, con exponentes $\alpha^2/[s_r(2\alpha+s_r)]$ y $\alpha^2/[s_r(2\alpha+s_b)]$. `proposicion310_dimension_ge_dos` especializa a $s_r=d$, $s_b=d-1$ y factor geométrico $\sqrt d$. La instancia $d=2$ recupera la declaración anterior con el mismo problema muestral, pesos, índices y cotas.

`corolario312_premisas310_dimensional` reutiliza la implicación funcional de C3.12 para ambos operadores. Usa los mismos prefijos y el mismo peso común de P3.10. `pesoRaizDimensional_tendsto` deduce el decaimiento del peso a partir del crecimiento de ambos tamaños. La aproximación fuerte descarga las cotas de comparación y (3.42) cuando la brecha de optimización es de la escala correspondiente. La construcción de comparadores o mínimos sigue siendo una obligación de la clase particular.

## Alcance restante

El [inventario](INVENTARIO_FORMAL_CAPITULO_III.md) distingue los casos unidimensional y multidimensional y la instancia del cuadrado. Los enunciados aquí probados son escalares. Quedan la traducción multiíndice de L3.1, la existencia clásica bajo H3.16, la generalización de L3.19 y T3.20 a dominios Lipschitz y la verificación geométrica de H3.2 para otros dominios concretos.

## Verificación

`lake build` completó 4030 trabajos con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. Los `#check` y `#print axioms` de los módulos nuevos se ejecutaron con la compilación. Las declaraciones principales dependen únicamente de `propext`, `Classical.choice` y `Quot.sound`. El escaneo del código Lean quedó limpio. El SHA-256 del PDF normativo sigue siendo `c6c612f7141c8c6ab5730fc0853b6d16222b97e5615e306f2e32191a49b686e0`.
