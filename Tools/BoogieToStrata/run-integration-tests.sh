#!/bin/bash

# BoogieToStrata Integration Test Runner
echo "Running BoogieToStrata Integration Tests..."
echo "========================================"

# Build the main project first
echo "Building BoogieToStrata project..."
dotnet build Source/BoogieToStrata.csproj

if [ $? -ne 0 ]; then
    echo "Failed to build main project. Exiting."
    exit 1
fi

LOG_ARGS=
#LOG_ARGS='--logger "console;verbosity=normal"'

# Build and run the integration tests
echo "Building and running integration tests..."
dotnet test IntegrationTests/BoogieToStrata.IntegrationTests.csproj $LOG_ARGS

echo "Integration tests completed."
