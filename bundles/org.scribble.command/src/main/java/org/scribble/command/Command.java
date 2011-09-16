/*
 * Copyright 2009 www.scribble.org
 * 
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
package org.scribble.command;

/**
 * This interface represents a command.
 *
 */
public interface Command {

    /**
     * This method returns the name of the command.
     * 
     * @return The name
     */
    public String getName();
    
    /**
     * This method returns the description.
     * 
     * @return The description
     */
    public String getDescription();
    
    /**
     * This method executes the command with the
     * given arguments.
     * 
     * @param args The arguments
     * @return Whether the command executed
     */
    public boolean execute(String[] args);
    
}
