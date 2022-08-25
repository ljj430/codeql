/**
 * @name Untrusted data passed to external API
 * @description Data provided remotely is used in this external API without sanitization, which could be a security risk.
 * @id cpp/untrusted-data-to-external-api-ir
 * @kind path-problem
 * @precision low
 * @problem.severity error
 * @security-severity 7.8
 * @tags security external/cwe/cwe-20
 */


import cpp
import semmle.code.cpp.ir.dataflow.TaintTracking
//import ir.ExternalAPIs
import semmle.code.cpp.security.FlowSources
import DataFlow::PathGraph
import semmle.code.cpp.ir.dataflow.TaintTracking
private import semmle.code.cpp.security.FlowSources
private import semmle.code.cpp.models.interfaces.DataFlow
private import semmle.code.cpp.models.interfaces.SideEffect
import semmle.code.cpp.valuenumbering.GlobalValueNumbering
/**
 * A `Function` that is considered a "safe" external API from a security perspective.
 */
abstract class SafeExternalApiFunction extends Function { }

/** DEPRECATED: Alias for SafeExternalApiFunction */
deprecated class SafeExternalAPIFunction = SafeExternalApiFunction;

/** The default set of "safe" external APIs. */
private class DefaultSafeExternalApiFunction extends SafeExternalApiFunction {
  DefaultSafeExternalApiFunction() {
    // If a function does not write to any of its arguments, we consider it safe to
    // pass untrusted data to it. This means that string functions such as `strcmp`
    // and `strlen`, as well as memory functions such as `memcmp`, are considered safe.
    exists(SideEffectFunction model | model = this |
      model.hasOnlySpecificWriteSideEffects() and
      not model.hasSpecificWriteSideEffect(_, _, _)
    )
  }
}


/** A node representing untrusted data being passed to an external API. */
class ExternalApiDataNode extends DataFlow::Node {
  Call call;
  int i;

  ExternalApiDataNode() {
    // Argument to call to a function
    (
      this.asExpr() = call.getArgument(i)
      or
      i = -1 and this.asExpr() = call.getQualifier()
    ) and
    exists(Function f |
      f = call.getTarget() and
      // Defined outside the source archive
      not f.hasDefinition() and
      // Not already modeled as a dataflow or taint step
      not f instanceof DataFlowFunction and
      not f instanceof TaintFunction and
      // Not a call to a known safe external API
      not f instanceof SafeExternalApiFunction
    )
  }

  /** Gets the called API `Function`. */
  Function getExternalFunction() { result = call.getTarget() }

  /** Gets the index which is passed untrusted data (where -1 indicates the qualifier). */
  int getIndex() { result = i }

  /** Gets the description of the function being called. */
  string getFunctionDescription() { result = this.getExternalFunction().toString() }
}

/** A configuration for tracking flow from `RemoteFlowSource`s to `ExternalApiDataNode`s. */
class UntrustedDataToExternalApiConfig extends TaintTracking::Configuration {
  UntrustedDataToExternalApiConfig() { this = "UntrustedDataToExternalAPIConfigIR" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  override predicate isSink(DataFlow::Node sink) { sink instanceof ExternalApiDataNode }
  
  override predicate isSanitizer(DataFlow::Node sanitizer) { 
	exists(FunctionCall fc |
    fc.getTarget().hasName("escape_html") and
    fc.getArgument(0).toString() = "username"
  )
  }
}

/** DEPRECATED: Alias for UntrustedDataToExternalApiConfig */
deprecated class UntrustedDataToExternalAPIConfig = UntrustedDataToExternalApiConfig;


from UntrustedDataToExternalApiConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink, source, sink,
  "Call to " + sink.getNode().(ExternalApiDataNode).getExternalFunction().toString() +
    " with untrusted data from $@.", source, source.getNode().(RemoteFlowSource).getSourceType()

