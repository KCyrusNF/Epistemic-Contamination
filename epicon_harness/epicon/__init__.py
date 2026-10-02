"""Epistemic Contamination — LLM evaluation pipeline and assistant GUI.

Public surface::

    from epicon import (
        TestCase, RunLog, ModelSpec, BatchRunner, RunnerConfig, Manifest,
        KeyringCredentialManager, export_sessions, export_results,
    )
"""

from __future__ import annotationsfrom .clients import ClientFactory, RetryPolicyfrom .conversation import Conversation, Messagefrom .credentials import KeyringCredentialManager, StaticCredentialStorefrom .errors import (    ApiError,    ConfigError,    CredentialError,    EpiconError,    MissingDependency,    ProviderError,    SchemaError,)from .export_excel import export_logs, export_results, export_sessionsfrom .manifest import Manifestfrom .model_spec import ModelSpec, ThinkingConfigfrom .models import (    CaseMetadata,    ConversationTurn,    EvaluationSummary,    ExpectedAnswer,    FormalArtifacts,    LoggedPrompt,    LoggedResponse,    ModelMetadata,    Prompt,    Reference,    ResearcherReview,    RunLog,    RunMetadata,    TestCase,    TestCaseRef,    Turn,    TurnEvaluation,    TurnUsage,    Usage,)from .providers import ProviderSpec, all_providers, get_providerfrom .runner import BatchResult, BatchRunner, ProgressEvent, RunnerConfigfrom .throttle import ThrottleSettings__version__ = "2.0.0"

__all__ = [
    "ApiError",
    "BatchResult",
    "BatchRunner",
    "CaseMetadata",
    "ClientFactory",
    "ConfigError",
    "Conversation",
    "ConversationTurn",
    "CredentialError",
    "EpiconError",
    "EvaluationSummary",
    "ExpectedAnswer",
    "FormalArtifacts",
    "KeyringCredentialManager",
    "LoggedPrompt",
    "LoggedResponse",
    "Manifest",
    "Message",
    "MissingDependency",
    "ModelMetadata",
    "ModelSpec",
    "ProgressEvent",
    "Prompt",
    "ProviderError",
    "ProviderSpec",
    "Reference",
    "ResearcherReview",
    "RetryPolicy",
    "RunLog",
    "RunMetadata",
    "RunnerConfig",
    "SchemaError",
    "StaticCredentialStore",
    "TestCase",
    "TestCaseRef",
    "ThinkingConfig",
    "ThrottleSettings",
    "Turn",
    "TurnEvaluation",
    "TurnUsage",
    "Usage",
    "__version__",
    "all_providers",
    "export_logs",
    "export_results",
    "export_sessions",
    "get_provider",
]
